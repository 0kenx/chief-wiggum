#!/usr/bin/env bash
set -euo pipefail
# Test log-rotation.sh: archival, rotation, pruning, and edge cases

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/log-rotation.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    mkdir -p "$TEST_DIR/logs"
    # Init module, then override defaults with test-friendly values
    export WIGGUM_LOG_ROTATE_LINES=100
    log_rotation_init "$TEST_DIR/logs"
    _LR_ENABLED="true"
    _LR_MAX_LINES=100
    _LR_MAX_ARCHIVES=10
}
teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Test: Small file is skipped (no rotation)
# =============================================================================
test_skip_small_file() {
    local log_file="$TEST_DIR/logs/small.log"
    # Create a 50-line file (below threshold of 100)
    local i
    for ((i = 1; i <= 50; i++)); do
        echo "line $i" >> "$log_file"
    done

    log_rotation_check "$log_file"

    # No archive should be created
    local archive_count
    archive_count=$(find "$TEST_DIR/logs/archive" -name "small.log.*.gz" 2>/dev/null | wc -l)
    archive_count="${archive_count// /}"
    assert_equals "0" "$archive_count" "Small file should not be rotated"

    # Original file should be unchanged
    local line_count
    line_count=$(wc -l < "$log_file")
    line_count="${line_count// /}"
    assert_equals "50" "$line_count" "Small file should keep all lines"
}

# =============================================================================
# Test: Large file is rotated and archive is valid gzip
# =============================================================================
test_rotate_large_file() {
    local log_file="$TEST_DIR/logs/orchestrator.log"
    # Create a 150-line file (above threshold of 100)
    local i
    for ((i = 1; i <= 150; i++)); do
        echo "[2024-01-26T10:30:00+0000] INFO: Log message number $i" >> "$log_file"
    done

    log_rotation_check "$log_file"

    # Archive should exist
    local archive_count
    archive_count=$(find "$TEST_DIR/logs/archive" -name "orchestrator.log.*.gz" 2>/dev/null | wc -l)
    archive_count="${archive_count// /}"
    assert_equals "1" "$archive_count" "Large file should produce one archive"

    # Original file should be truncated (empty)
    local line_count
    line_count=$(wc -l < "$log_file")
    line_count="${line_count// /}"
    assert_equals "0" "$line_count" "Rotated file should be empty"

    # Archive should be valid gzip with original content
    local archive_file
    archive_file=$(find "$TEST_DIR/logs/archive" -name "orchestrator.log.*.gz" | head -1)
    assert_success "Archive should be valid gzip" gzip -t "$archive_file"

    local archived_lines
    archived_lines=$(gzip -dc "$archive_file" | wc -l)
    archived_lines="${archived_lines// /}"
    assert_equals "150" "$archived_lines" "Archive should contain all 150 lines"
}

# =============================================================================
# Test: Archive naming format
# =============================================================================
test_archive_naming() {
    local log_file="$TEST_DIR/logs/test.log"
    local i
    for ((i = 1; i <= 150; i++)); do
        echo "line $i" >> "$log_file"
    done

    log_rotation_check "$log_file"

    local archive_file
    archive_file=$(find "$TEST_DIR/logs/archive" -name "test.log.*.gz" | head -1)
    assert_not_empty "$archive_file" "Archive file should exist"

    # Verify naming pattern: basename.epoch.gz
    local archive_basename
    archive_basename=$(basename "$archive_file")
    if [[ "$archive_basename" =~ ^test\.log\.[0-9]+\.gz$ ]]; then
        echo -e "  ${GREEN}✓${NC} Archive name matches expected pattern"
        ((++ASSERTION_COUNT))
    else
        echo -e "  ${RED}✗${NC} Archive name should match test.log.<epoch>.gz, got: $archive_basename" >&2
        ((++ASSERTION_COUNT))
        ((++FAILED_ASSERTIONS))
    fi
}

# =============================================================================
# Test: Audit log header preservation
# =============================================================================
test_audit_log_header_preservation() {
    local log_file="$TEST_DIR/logs/audit.log"
    # Create audit log with header
    cat > "$log_file" << 'EOF'
# Audit Log
# Project: /test/project
# Started: 2024-01-26T10:00:00
============================
entry1: data
entry2: data
EOF
    # Add enough data lines to trigger rotation
    local i
    for ((i = 1; i <= 150; i++)); do
        echo "audit entry $i" >> "$log_file"
    done

    log_rotation_check "$log_file"

    # Header should be preserved in the live file
    assert_file_contains "$log_file" "# Audit Log" "Header line 1 should be preserved"
    assert_file_contains "$log_file" "============================" "Header separator should be preserved"

    # Data lines should NOT be in the live file
    assert_file_not_contains "$log_file" "audit entry 1" "Data should be archived, not in live file"

    # Live file should only have header lines
    local line_count
    line_count=$(wc -l < "$log_file")
    line_count="${line_count// /}"
    assert_equals "4" "$line_count" "Live file should only contain 4 header lines"

    # Archive should contain the data lines
    local archive_file
    archive_file=$(find "$TEST_DIR/logs/archive" -name "audit.log.*.gz" | head -1)
    assert_not_empty "$archive_file" "Audit archive should exist"

    local archived_content
    archived_content=$(gzip -dc "$archive_file")
    assert_output_contains "$archived_content" "audit entry 1" "Archive should contain data lines"
    assert_output_not_contains "$archived_content" "# Audit Log" "Archive should not contain header"
}

# =============================================================================
# Test: Pruning old archives beyond max_archives
# =============================================================================
test_prune_old_archives() {
    _LR_MAX_ARCHIVES=3

    local log_file="$TEST_DIR/logs/prune.log"

    # Pre-create 3 old archives with known epochs
    local base_epoch=1700000000
    local j
    for ((j = 0; j < 3; j++)); do
        local epoch=$((base_epoch + j * 100))
        echo "old data $j" | gzip > "$TEST_DIR/logs/archive/prune.log.${epoch}.gz"
    done

    # Verify we have 3 archives
    local count
    count=$(find "$TEST_DIR/logs/archive" -name "prune.log.*.gz" | wc -l)
    count="${count// /}"
    assert_equals "3" "$count" "Should start with 3 archives"

    # Now create a file that triggers rotation (creates archive #4)
    local i
    for ((i = 1; i <= 150; i++)); do
        echo "line $i" >> "$log_file"
    done
    log_rotation_check "$log_file"

    # Should have been pruned to max_archives (3)
    count=$(find "$TEST_DIR/logs/archive" -name "prune.log.*.gz" | wc -l)
    count="${count// /}"
    assert_equals "3" "$count" "Should be pruned to max_archives (3)"

    # The oldest archive (base_epoch) should have been removed
    assert_file_not_exists "$TEST_DIR/logs/archive/prune.log.${base_epoch}.gz" \
        "Oldest archive should be pruned"
}

# =============================================================================
# Test: Rotation disabled via env var
# =============================================================================
test_disabled_via_env() {
    _LR_ENABLED="false"

    local log_file="$TEST_DIR/logs/disabled.log"
    local i
    for ((i = 1; i <= 150; i++)); do
        echo "line $i" >> "$log_file"
    done

    log_rotation_check_all

    # No archive should be created
    local archive_count
    archive_count=$(find "$TEST_DIR/logs/archive" -name "disabled.log.*.gz" 2>/dev/null | wc -l)
    archive_count="${archive_count// /}"
    assert_equals "0" "$archive_count" "Disabled rotation should not archive"

    # Original should be untouched
    local line_count
    line_count=$(wc -l < "$log_file")
    line_count="${line_count// /}"
    assert_equals "150" "$line_count" "Disabled rotation should not truncate"
}

# =============================================================================
# Test: JSONL file rotation
# =============================================================================
test_jsonl_rotation() {
    local log_file="$TEST_DIR/logs/activity.jsonl"
    local i
    for ((i = 1; i <= 150; i++)); do
        echo "{\"event\":\"test\",\"seq\":$i}" >> "$log_file"
    done

    log_rotation_check_all

    # Archive should exist
    local archive_count
    archive_count=$(find "$TEST_DIR/logs/archive" -name "activity.jsonl.*.gz" 2>/dev/null | wc -l)
    archive_count="${archive_count// /}"
    assert_equals "1" "$archive_count" "JSONL file should be rotated"

    # Original should be empty
    local line_count
    line_count=$(wc -l < "$log_file")
    line_count="${line_count// /}"
    assert_equals "0" "$line_count" "Rotated JSONL should be empty"
}

# =============================================================================
# Test: check_all iterates multiple files
# =============================================================================
test_check_all_multiple_files() {
    # Create two large files and one small file
    local i
    for ((i = 1; i <= 150; i++)); do
        echo "line $i" >> "$TEST_DIR/logs/one.log"
        echo "line $i" >> "$TEST_DIR/logs/two.log"
    done
    for ((i = 1; i <= 50; i++)); do
        echo "line $i" >> "$TEST_DIR/logs/small.log"
    done

    log_rotation_check_all

    local count_one count_two count_small
    count_one=$(find "$TEST_DIR/logs/archive" -name "one.log.*.gz" | wc -l)
    count_two=$(find "$TEST_DIR/logs/archive" -name "two.log.*.gz" | wc -l)
    count_small=$(find "$TEST_DIR/logs/archive" -name "small.log.*.gz" | wc -l)
    count_one="${count_one// /}"
    count_two="${count_two// /}"
    count_small="${count_small// /}"

    assert_equals "1" "$count_one" "one.log should be rotated"
    assert_equals "1" "$count_two" "two.log should be rotated"
    assert_equals "0" "$count_small" "small.log should not be rotated"
}

# =============================================================================
# Test: Nonexistent file is handled gracefully
# =============================================================================
test_nonexistent_file() {
    local exit_code=0
    log_rotation_check "$TEST_DIR/logs/nonexistent.log" || exit_code=$?
    assert_equals "0" "$exit_code" "Nonexistent file should return 0 (no-op)"
}

# =============================================================================
# Test: Fast-path skips wc -l for small byte-size files
# =============================================================================
test_fast_path_byte_check() {
    local log_file="$TEST_DIR/logs/fastpath.log"
    # Create a file with short lines that is under byte threshold
    # 80 lines * 5 bytes/line = 400 bytes, threshold = 100 * 80 = 8000
    local i
    for ((i = 1; i <= 80; i++)); do
        echo "hi" >> "$log_file"
    done

    log_rotation_check "$log_file"

    local archive_count
    archive_count=$(find "$TEST_DIR/logs/archive" -name "fastpath.log.*.gz" 2>/dev/null | wc -l)
    archive_count="${archive_count// /}"
    assert_equals "0" "$archive_count" "Fast-path should skip small files"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_skip_small_file
run_test test_rotate_large_file
run_test test_archive_naming
run_test test_audit_log_header_preservation
run_test test_prune_old_archives
run_test test_disabled_via_env
run_test test_jsonl_rotation
run_test test_check_all_multiple_files
run_test test_nonexistent_file
run_test test_fast_path_byte_check

print_test_summary
exit_with_test_result
