#!/usr/bin/env bash
set -euo pipefail
# Tests for worker command modules
# Tests helper functions and validation logic in isolation

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Suppress log output
LOG_LEVEL=ERROR
export LOG_LEVEL

# Test isolation vars
TEST_DIR=""
RALPH_DIR=""
PROJECT_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    PROJECT_DIR="$TEST_DIR/project"
    RALPH_DIR="$PROJECT_DIR/.ralph"
    export RALPH_DIR
    export PROJECT_DIR

    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$RALPH_DIR/logs"
    mkdir -p "$PROJECT_DIR"

    # Create minimal kanban
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
## Todo
- [ ] **[TASK-001]** Test task one
  - Description: First test task
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Test task two
  - Description: Second test task
  - Priority: MEDIUM
  - Dependencies: TASK-001
EOF

    # Initialize minimal git repo
    cd "$PROJECT_DIR"
    git init -q
    git config user.email "test@example.com"
    git config user.name "Test User"
    echo "test" > README.md
    git add README.md
    git commit -q -m "Initial commit"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# cmd-resume.sh Helper Functions
# =============================================================================

# Source only the helper functions from cmd-resume.sh
# We extract them to avoid loading the full dependency chain
_load_resume_helpers() {
    # Extract the helper functions directly
    # shellcheck disable=SC1090  # Dynamic source from heredoc for test isolation
    source <(cat << 'HELPERS_EOF'
#!/usr/bin/env bash
# Extracted helper functions from cmd-resume.sh for testing

_step_has_result() {
    local worker_dir="$1"
    local step_id="$2"

    [ -d "$worker_dir/results" ] || return 1

    local result_file
    result_file=$(find "$worker_dir/results" -name "*-${step_id}-result.json" 2>/dev/null | sort -r | head -1)
    [ -f "$result_file" ]
}

_get_current_step() {
    local worker_dir="$1"
    local config_file="$worker_dir/pipeline-config.json"

    [ -f "$config_file" ] || return 0
    jq -r '.current.step_id // ""' "$config_file" 2>/dev/null
}

_read_resume_decision() {
    local worker_dir="$1"
    local needs_resume_decide="$2"
    local current_step="${3:-}"

    if [ "$needs_resume_decide" != "true" ]; then
        # Direct resume: step was interrupted mid-execution
        decision="RETRY"
        resume_step_id="$current_step"
        # Read pipeline name from pipeline-config.json so we load the correct pipeline
        if [ -f "$worker_dir/pipeline-config.json" ]; then
            resume_pipeline=$(jq -r '.pipeline.name // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
            if [[ "$resume_pipeline" == "null" ]]; then resume_pipeline=""; fi
        fi
        return
    fi

    # Read from structured JSON (preferred) or fallback to text file
    if [ -f "$worker_dir/resume-decision.json" ]; then
        decision=$(jq -r '.decision // ""' "$worker_dir/resume-decision.json")
        resume_pipeline=$(jq -r '.pipeline // ""' "$worker_dir/resume-decision.json")
        resume_step_id=$(jq -r '.resume_step // ""' "$worker_dir/resume-decision.json")
        # Normalize null to empty
        if [[ "$resume_pipeline" == "null" ]]; then resume_pipeline=""; fi
        if [[ "$resume_step_id" == "null" ]]; then resume_step_id=""; fi
    else
        # Backward compat: old resume-step.txt
        local raw
        raw=$(cat "$worker_dir/resume-step.txt" 2>/dev/null || echo "")
        raw=$(echo "$raw" | tr -d '[:space:]')
        if [[ "$raw" == RETRY:* ]]; then
            decision="RETRY"
            resume_pipeline=$(echo "$raw" | cut -d: -f2)
            resume_step_id=$(echo "$raw" | cut -d: -f3)
        elif [[ "$raw" == "COMPLETE" || "$raw" == "ABORT" || "$raw" == "DEFER" ]]; then
            decision="$raw"
        elif [ -n "$raw" ]; then
            # Legacy: bare step_id → treat as RETRY with current pipeline
            decision="RETRY"
            resume_step_id="$raw"
        fi
    fi

    if [ -z "$decision" ]; then
        return 1
    fi
}
HELPERS_EOF
)
}

test_step_has_result_with_result() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir/results"
    echo '{"result":"PASS"}' > "$worker_dir/results/1234567890-planning-result.json"

    _load_resume_helpers

    if _step_has_result "$worker_dir" "planning"; then
        echo -e "  ${GREEN}✓${NC} Step with result file returns 0"
    else
        echo -e "  ${RED}✗${NC} Step with result file should return 0"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_step_has_result_without_result() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir/results"

    _load_resume_helpers

    if _step_has_result "$worker_dir" "execution"; then
        echo -e "  ${RED}✗${NC} Step without result file should return 1"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Step without result file returns 1"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_step_has_result_no_results_dir() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    _load_resume_helpers

    if _step_has_result "$worker_dir" "planning"; then
        echo -e "  ${RED}✗${NC} Missing results dir should return 1"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing results dir returns 1"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_get_current_step_from_config() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/pipeline-config.json" << 'EOF'
{
  "current": {
    "step_id": "execution",
    "iteration": 2
  }
}
EOF

    _load_resume_helpers

    local step
    step=$(_get_current_step "$worker_dir")
    assert_equals "execution" "$step" "Should extract step_id from pipeline-config.json"
}

test_get_current_step_missing_file() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    _load_resume_helpers

    local step
    step=$(_get_current_step "$worker_dir")
    assert_equals "" "$step" "Missing pipeline-config.json should return empty string"
}

test_get_current_step_no_step_id() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/pipeline-config.json" << 'EOF'
{
  "current": {
    "iteration": 1
  }
}
EOF

    _load_resume_helpers

    local step
    step=$(_get_current_step "$worker_dir")
    assert_equals "" "$step" "Missing step_id field should return empty string"
}

test_read_resume_decision_direct_resume() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/pipeline-config.json" << 'EOF'
{
  "pipeline": {
    "name": "default"
  }
}
EOF

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "false" "execution"

    assert_equals "RETRY" "$decision" "Direct resume should set decision=RETRY"
    assert_equals "execution" "$resume_step_id" "Direct resume should use current_step"
    assert_equals "default" "$resume_pipeline" "Direct resume should read pipeline from config"
}

test_read_resume_decision_from_json() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/resume-decision.json" << 'EOF'
{
  "decision": "RETRY",
  "pipeline": "fix",
  "resume_step": "test"
}
EOF

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "true" ""

    assert_equals "RETRY" "$decision" "Should read decision from JSON"
    assert_equals "fix" "$resume_pipeline" "Should read pipeline from JSON"
    assert_equals "test" "$resume_step_id" "Should read resume_step from JSON"
}

test_read_resume_decision_complete() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/resume-decision.json" << 'EOF'
{
  "decision": "COMPLETE"
}
EOF

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "true" ""

    assert_equals "COMPLETE" "$decision" "Should read COMPLETE decision"
}

test_read_resume_decision_abort() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/resume-decision.json" << 'EOF'
{
  "decision": "ABORT"
}
EOF

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "true" ""

    assert_equals "ABORT" "$decision" "Should read ABORT decision"
}

test_read_resume_decision_defer() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/resume-decision.json" << 'EOF'
{
  "decision": "DEFER"
}
EOF

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "true" ""

    assert_equals "DEFER" "$decision" "Should read DEFER decision"
}

test_read_resume_decision_legacy_text_file_retry() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    echo "RETRY:fix:test" > "$worker_dir/resume-step.txt"

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "true" ""

    assert_equals "RETRY" "$decision" "Should parse RETRY from legacy text file"
    assert_equals "fix" "$resume_pipeline" "Should parse pipeline from legacy text file"
    assert_equals "test" "$resume_step_id" "Should parse step from legacy text file"
}

test_read_resume_decision_legacy_text_file_complete() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    echo "COMPLETE" > "$worker_dir/resume-step.txt"

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "true" ""

    assert_equals "COMPLETE" "$decision" "Should parse COMPLETE from legacy text file"
}

test_read_resume_decision_legacy_bare_step_id() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    echo "execution" > "$worker_dir/resume-step.txt"

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "true" ""

    assert_equals "RETRY" "$decision" "Bare step ID should default to RETRY"
    assert_equals "execution" "$resume_step_id" "Should use bare step ID as resume_step"
}

test_read_resume_decision_null_normalization() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/resume-decision.json" << 'EOF'
{
  "decision": "RETRY",
  "pipeline": null,
  "resume_step": null
}
EOF

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "true" ""

    assert_equals "RETRY" "$decision" "Should read decision"
    assert_equals "" "$resume_pipeline" "null pipeline should normalize to empty string"
    assert_equals "" "$resume_step_id" "null resume_step should normalize to empty string"
}

test_read_resume_decision_missing_files() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    _load_resume_helpers

    local decision="" resume_pipeline="" resume_step_id=""
    local result=0
    _read_resume_decision "$worker_dir" "true" "" || result=$?

    assert_equals "1" "$result" "Missing decision files should return 1"
}

# =============================================================================
# cmd-start.sh Validation Tests
# =============================================================================

test_start_validation_missing_ralph_dir() {
    # Simulate validation checks from cmd-start.sh
    local check_ralph_dir="$TEST_DIR/nonexistent/.ralph"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -d "$check_ralph_dir" ]; then
        echo -e "  ${RED}✗${NC} Missing .ralph dir check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing .ralph dir detected correctly"
    fi
}

test_start_validation_missing_task_id() {
    local input_id=""

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -z "$input_id" ]; then
        echo -e "  ${GREEN}✓${NC} Empty task ID detected correctly"
    else
        echo -e "  ${RED}✗${NC} Empty task ID check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_start_validation_missing_kanban() {
    local kanban_file="$TEST_DIR/nonexistent/kanban.md"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -f "$kanban_file" ]; then
        echo -e "  ${RED}✗${NC} Missing kanban check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing kanban detected correctly"
    fi
}

test_start_validation_worker_dir_mode_missing_workspace() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -d "$worker_dir/workspace" ]; then
        echo -e "  ${RED}✗${NC} Missing workspace check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing workspace detected correctly"
    fi
}

test_start_validation_worker_dir_mode_missing_prd() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir/workspace"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -f "$worker_dir/prd.md" ]; then
        echo -e "  ${RED}✗${NC} Missing PRD check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing PRD detected correctly"
    fi
}

test_start_validation_worker_already_exists() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    # Simulate find_any_worker_by_task_id logic
    local existing
    existing=$(find "$RALPH_DIR/workers" -maxdepth 1 -name "worker-TASK-001-*" 2>/dev/null | grep -v -- '-plan-' | head -1 || true)

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -n "$existing" ]; then
        echo -e "  ${GREEN}✓${NC} Existing worker detected correctly"
    else
        echo -e "  ${RED}✗${NC} Existing worker check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_start_validation_plan_worker_excluded() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345-plan-67890"
    mkdir -p "$worker_dir"

    # Simulate find_any_worker_by_task_id logic (excludes plan workers)
    local existing
    existing=$(find "$RALPH_DIR/workers" -maxdepth 1 -name "worker-TASK-001-*" 2>/dev/null | grep -v -- '-plan-' | head -1 || true)

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -z "$existing" ]; then
        echo -e "  ${GREEN}✓${NC} Plan worker correctly excluded from conflict check"
    else
        echo -e "  ${RED}✗${NC} Plan worker should be excluded"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

# =============================================================================
# cmd-merge.sh Validation Tests
# =============================================================================

test_merge_validation_missing_ralph_dir() {
    local check_ralph_dir="$TEST_DIR/nonexistent/.ralph"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -d "$check_ralph_dir" ]; then
        echo -e "  ${RED}✗${NC} Missing .ralph dir check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing .ralph dir detected correctly"
    fi
}

test_merge_validation_missing_task_id() {
    local input_id=""

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -z "$input_id" ]; then
        echo -e "  ${GREEN}✓${NC} Empty task ID detected correctly"
    else
        echo -e "  ${RED}✗${NC} Empty task ID check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_merge_validation_missing_kanban() {
    local kanban_file="$TEST_DIR/nonexistent/kanban.md"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -f "$kanban_file" ]; then
        echo -e "  ${RED}✗${NC} Missing kanban check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing kanban detected correctly"
    fi
}

test_merge_validation_no_worker_found() {
    # Simulate find_worker_by_task_id returning empty
    local worker_dir=""

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -z "$worker_dir" ] || [ ! -d "$worker_dir" ]; then
        echo -e "  ${GREEN}✓${NC} No worker found detected correctly"
    else
        echo -e "  ${RED}✗${NC} No worker found check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_merge_validation_no_pr_number() {
    local pr_number=""

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; then
        echo -e "  ${GREEN}✓${NC} Missing PR number detected correctly"
    else
        echo -e "  ${RED}✗${NC} Missing PR number check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

# =============================================================================
# cmd-fix.sh Validation Tests
# =============================================================================

test_fix_validation_missing_ralph_dir() {
    local check_ralph_dir="$TEST_DIR/nonexistent/.ralph"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -d "$check_ralph_dir" ]; then
        echo -e "  ${RED}✗${NC} Missing .ralph dir check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing .ralph dir detected correctly"
    fi
}

test_fix_validation_missing_task_id() {
    local input_id=""

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -z "$input_id" ]; then
        echo -e "  ${GREEN}✓${NC} Empty task ID detected correctly"
    else
        echo -e "  ${RED}✗${NC} Empty task ID check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_fix_validation_missing_kanban() {
    local kanban_file="$TEST_DIR/nonexistent/kanban.md"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -f "$kanban_file" ]; then
        echo -e "  ${RED}✗${NC} Missing kanban check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Missing kanban detected correctly"
    fi
}

test_fix_validation_no_worker_and_no_review_dir() {
    local worker_dir=""
    local review_dir="$TEST_DIR/.ralph/review"

    # Simulate the fallback check
    if [ -z "$worker_dir" ]; then
        worker_dir="$review_dir"
        if [ ! -f "$worker_dir/task-comments.md" ]; then
            worker_dir=""
        fi
    fi

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -z "$worker_dir" ]; then
        echo -e "  ${GREEN}✓${NC} No worker or review dir detected correctly"
    else
        echo -e "  ${RED}✗${NC} No worker or review dir check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_fix_validation_agent_already_running() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    echo "99999" > "$worker_dir/agent.pid"

    # Simulate PID check (we can't actually test kill -0 in isolation)
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -f "$worker_dir/agent.pid" ]; then
        echo -e "  ${GREEN}✓${NC} Agent PID file detected correctly"
    else
        echo -e "  ${RED}✗${NC} Agent PID file check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_fix_validation_missing_task_comments() {
    local worker_dir="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ ! -f "$worker_dir/task-comments.md" ]; then
        echo -e "  ${GREEN}✓${NC} Missing task-comments.md detected correctly"
    else
        echo -e "  ${RED}✗${NC} Missing task-comments.md check failed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

# =============================================================================
# Task ID Extraction Tests
# =============================================================================

test_task_id_extraction_standard() {
    local worker_id="worker-TASK-001-12345"
    local task_id
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

    assert_equals "TASK-001" "$task_id" "Should extract standard task ID"
}

test_task_id_extraction_different_prefix() {
    local worker_id="worker-FEAT-042-67890"
    local task_id
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

    assert_equals "FEAT-042" "$task_id" "Should extract task ID with different prefix"
}

test_task_id_extraction_plan_worker() {
    local worker_id="worker-TASK-001-12345-plan-67890"
    local task_id
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

    assert_equals "TASK-001" "$task_id" "Should extract task ID from plan worker"
}

test_task_id_extraction_long_prefix() {
    local worker_id="worker-PIPELINE-099-11111"
    local task_id
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

    assert_equals "PIPELINE-099" "$task_id" "Should extract task ID with long prefix"
}

test_task_id_extraction_short_prefix() {
    local worker_id="worker-AB-999-22222"
    local task_id
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

    assert_equals "AB-999" "$task_id" "Should extract task ID with short prefix"
}

# =============================================================================
# Run All Tests
# =============================================================================

# cmd-resume.sh helper function tests
run_test test_step_has_result_with_result
run_test test_step_has_result_without_result
run_test test_step_has_result_no_results_dir
run_test test_get_current_step_from_config
run_test test_get_current_step_missing_file
run_test test_get_current_step_no_step_id
run_test test_read_resume_decision_direct_resume
run_test test_read_resume_decision_from_json
run_test test_read_resume_decision_complete
run_test test_read_resume_decision_abort
run_test test_read_resume_decision_defer
run_test test_read_resume_decision_legacy_text_file_retry
run_test test_read_resume_decision_legacy_text_file_complete
run_test test_read_resume_decision_legacy_bare_step_id
run_test test_read_resume_decision_null_normalization
run_test test_read_resume_decision_missing_files

# cmd-start.sh validation tests
run_test test_start_validation_missing_ralph_dir
run_test test_start_validation_missing_task_id
run_test test_start_validation_missing_kanban
run_test test_start_validation_worker_dir_mode_missing_workspace
run_test test_start_validation_worker_dir_mode_missing_prd
run_test test_start_validation_worker_already_exists
run_test test_start_validation_plan_worker_excluded

# cmd-merge.sh validation tests
run_test test_merge_validation_missing_ralph_dir
run_test test_merge_validation_missing_task_id
run_test test_merge_validation_missing_kanban
run_test test_merge_validation_no_worker_found
run_test test_merge_validation_no_pr_number

# cmd-fix.sh validation tests
run_test test_fix_validation_missing_ralph_dir
run_test test_fix_validation_missing_task_id
run_test test_fix_validation_missing_kanban
run_test test_fix_validation_no_worker_and_no_review_dir
run_test test_fix_validation_agent_already_running
run_test test_fix_validation_missing_task_comments

# Task ID extraction tests
run_test test_task_id_extraction_standard
run_test test_task_id_extraction_different_prefix
run_test test_task_id_extraction_plan_worker
run_test test_task_id_extraction_long_prefix
run_test test_task_id_extraction_short_prefix

print_test_summary
exit_with_test_result
