#!/usr/bin/env bash
set -euo pipefail
# Tests for distributed coordination modules

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

LOG_LEVEL=ERROR
export LOG_LEVEL

TEST_DIR=""
MOCK_GH_DIR=""

# Mock gh data structures
declare -A MOCK_GH_ISSUE_LABELS
declare -A MOCK_GH_ISSUE_ASSIGNEES
declare -A MOCK_GH_ISSUE_COMMENTS
declare -A MOCK_GH_ISSUE_EXISTS

setup() {
    TEST_DIR=$(mktemp -d)
    MOCK_GH_DIR=$(mktemp -d)

    # Reset mock data
    MOCK_GH_ISSUE_LABELS=()
    MOCK_GH_ISSUE_ASSIGNEES=()
    MOCK_GH_ISSUE_COMMENTS=()
    MOCK_GH_ISSUE_EXISTS=()

    # Create mock gh script
    cat > "$MOCK_GH_DIR/gh" << 'MOCK_GH_EOF'
#!/usr/bin/env bash
set -euo pipefail

# Mock GitHub CLI for testing
# Reads/writes from temp files to simulate GitHub state

MOCK_DATA_DIR="${MOCK_GH_DATA_DIR:-/tmp/mock-gh-data}"
mkdir -p "$MOCK_DATA_DIR"

# Helper: get labels file for issue
get_labels_file() {
    echo "$MOCK_DATA_DIR/issue-$1-labels.txt"
}

# Helper: get assignees file for issue
get_assignees_file() {
    echo "$MOCK_DATA_DIR/issue-$1-assignees.txt"
}

# Helper: get comments file for issue
get_comments_file() {
    echo "$MOCK_DATA_DIR/issue-$1-comments.jsonl"
}

# Helper: initialize issue if not exists
init_issue() {
    local issue="$1"
    local labels_file assignees_file comments_file
    labels_file=$(get_labels_file "$issue")
    assignees_file=$(get_assignees_file "$issue")
    comments_file=$(get_comments_file "$issue")

    [ -f "$labels_file" ] || touch "$labels_file"
    [ -f "$assignees_file" ] || touch "$assignees_file"
    [ -f "$comments_file" ] || echo '[]' > "$comments_file"
}

case "$1" in
    issue)
        case "$2" in
            edit)
                # Parse issue number
                issue_num="$3"
                shift 3

                init_issue "$issue_num"
                labels_file=$(get_labels_file "$issue_num")
                assignees_file=$(get_assignees_file "$issue_num")

                # Process flags
                while [ $# -gt 0 ]; do
                    case "$1" in
                        --add-label)
                            echo "$2" >> "$labels_file"
                            shift 2
                            ;;
                        --remove-label)
                            grep -vxF "$2" "$labels_file" > "${labels_file}.tmp" || true
                            mv "${labels_file}.tmp" "$labels_file"
                            shift 2
                            ;;
                        --add-assignee)
                            if [ "$2" = "@me" ]; then
                                echo "testuser" >> "$assignees_file"
                            else
                                echo "$2" >> "$assignees_file"
                            fi
                            shift 2
                            ;;
                        --remove-assignee)
                            if [ "$2" = "@me" ]; then
                                grep -vxF "testuser" "$assignees_file" > "${assignees_file}.tmp" || true
                            else
                                grep -vxF "$2" "$assignees_file" > "${assignees_file}.tmp" || true
                            fi
                            mv "${assignees_file}.tmp" "$assignees_file"
                            shift 2
                            ;;
                        *)
                            shift
                            ;;
                    esac
                done
                ;;

            view)
                issue_num="$3"
                shift 3

                init_issue "$issue_num"
                labels_file=$(get_labels_file "$issue_num")
                assignees_file=$(get_assignees_file "$issue_num")
                comments_file=$(get_comments_file "$issue_num")

                # Parse output format flags
                format=""
                jq_query=""
                while [ $# -gt 0 ]; do
                    case "$1" in
                        --json)
                            format="$2"
                            shift 2
                            ;;
                        -q|--jq)
                            jq_query="$2"
                            shift 2
                            ;;
                        *)
                            shift
                            ;;
                    esac
                done

                if [ "$format" = "labels" ]; then
                    # Build full JSON structure with labels
                    labels_json=$(jq -R -s -c 'split("\n") | map(select(length > 0)) | map({name: .})' < "$labels_file")
                    # Apply jq query to full structure
                    echo "{\"labels\": $labels_json}" | jq -r "$jq_query"
                elif [ "$format" = "assignees" ]; then
                    # Build full JSON structure with assignees
                    assignees_json=$(jq -R -s -c 'split("\n") | map(select(length > 0)) | map({login: .})' < "$assignees_file")
                    # Apply jq query to full structure
                    echo "{\"assignees\": $assignees_json}" | jq -r "$jq_query"
                elif [ "$format" = "comments" ]; then
                    # Build full JSON structure with comments
                    comments_json=$(cat "$comments_file")
                    if [ -n "$jq_query" ]; then
                        echo "{\"comments\": $comments_json}" | jq "$jq_query"
                    else
                        echo "{\"comments\": $comments_json}"
                    fi
                else
                    # Full issue view
                    jq -n \
                        --argjson labels "$(jq -R -s -c 'split("\n") | map(select(length > 0)) | map({name: .})' < "$labels_file")" \
                        --argjson assignees "$(jq -R -s -c 'split("\n") | map(select(length > 0)) | map({login: .})' < "$assignees_file")" \
                        --argjson comments "$(cat "$comments_file")" \
                        '{labels: $labels, assignees: $assignees, comments: $comments}'
                fi
                ;;

            comment)
                issue_num="$3"
                shift 3

                init_issue "$issue_num"
                comments_file=$(get_comments_file "$issue_num")

                # Parse body
                body=""
                while [ $# -gt 0 ]; do
                    case "$1" in
                        --body)
                            body="$2"
                            shift 2
                            ;;
                        *)
                            shift
                            ;;
                    esac
                done

                # Add comment to file
                local comment_id
                comment_id=$(date +%s)$$
                local timestamp
                timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
                jq -n \
                    --argjson id "$comment_id" \
                    --arg body "$body" \
                    --arg timestamp "$timestamp" \
                    '{databaseId: $id, body: $body, createdAt: $timestamp}' | \
                    jq -s ". + [$(cat "$comments_file")]" | \
                    jq 'flatten' > "${comments_file}.tmp"
                mv "${comments_file}.tmp" "$comments_file"
                ;;

            list)
                # Parse flags
                local label_filter=""
                local state_filter="open"
                local limit=100
                shift 2

                while [ $# -gt 0 ]; do
                    case "$1" in
                        --label)
                            label_filter="$2"
                            shift 2
                            ;;
                        --state)
                            state_filter="$2"
                            shift 2
                            ;;
                        --json)
                            # Ignore format
                            shift 2
                            ;;
                        --jq)
                            # Ignore jq
                            shift 2
                            ;;
                        --limit)
                            limit="$2"
                            shift 2
                            ;;
                        *)
                            shift
                            ;;
                    esac
                done

                # Find matching issues
                echo "[]"
                ;;
            *)
                echo "Unknown issue command: $2" >&2
                exit 1
                ;;
        esac
        ;;

    api)
        # Mock API calls
        shift
        method="GET"
        path=""
        body=""

        while [ $# -gt 0 ]; do
            case "$1" in
                --method)
                    method="$2"
                    shift 2
                    ;;
                -f)
                    shift 2
                    ;;
                *)
                    path="$1"
                    shift
                    ;;
            esac
        done

        # Return success for PATCH operations
        echo '{"success": true}'
        ;;

    *)
        echo "Unknown gh command: $1" >&2
        exit 1
        ;;
esac
MOCK_GH_EOF

    chmod +x "$MOCK_GH_DIR/gh"

    # Set environment to use mock
    export PATH="$MOCK_GH_DIR:$PATH"
    export MOCK_GH_DATA_DIR="$TEST_DIR/gh-data"
    mkdir -p "$MOCK_GH_DATA_DIR"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
    [ -n "$MOCK_GH_DIR" ] && rm -rf "$MOCK_GH_DIR"
}

# =============================================================================
# Helper Functions
# =============================================================================

# Initialize a mock issue with labels
mock_issue_add_label() {
    local issue_num="$1"
    local label="$2"
    echo "$label" >> "$MOCK_GH_DATA_DIR/issue-$issue_num-labels.txt"
}

# Initialize a mock issue
mock_issue_init() {
    local issue_num="$1"
    touch "$MOCK_GH_DATA_DIR/issue-$issue_num-labels.txt"
    touch "$MOCK_GH_DATA_DIR/issue-$issue_num-assignees.txt"
    echo '[]' > "$MOCK_GH_DATA_DIR/issue-$issue_num-comments.jsonl"
}

# Add a heartbeat comment to mock issue
mock_issue_add_heartbeat() {
    local issue_num="$1"
    local server_id="$2"
    local timestamp="$3"

    local comment_id
    comment_id=$(date +%s)$$
    local body
    body="<!-- wiggum:heartbeat -->
**Server:** $server_id
**Last Update:** $timestamp
**Pipeline Step:** test"

    jq -n \
        --argjson id "$comment_id" \
        --arg body "$body" \
        --arg timestamp "$timestamp" \
        '{databaseId: $id, body: $body, createdAt: $timestamp}' | \
        jq -s ". + [$(cat "$MOCK_GH_DATA_DIR/issue-$issue_num-comments.jsonl")]" | \
        jq 'flatten' > "$MOCK_GH_DATA_DIR/issue-$issue_num-comments.jsonl.tmp"
    mv "$MOCK_GH_DATA_DIR/issue-$issue_num-comments.jsonl.tmp" \
       "$MOCK_GH_DATA_DIR/issue-$issue_num-comments.jsonl"
}

# =============================================================================
# claim-manager.sh Tests
# =============================================================================

test_claim_get_owner_returns_server_id() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123
    mock_issue_add_label 123 "wiggum:server:test-server-1"

    local owner
    owner=$(claim_get_owner 123)
    assert_equals "test-server-1" "$owner" "claim_get_owner should extract server ID from label"
    teardown
}

test_claim_get_owner_returns_empty_when_no_server() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123
    mock_issue_add_label 123 "wiggum:task"

    local owner
    owner=$(claim_get_owner 123)
    assert_equals "" "$owner" "claim_get_owner should return empty when no server label"
    teardown
}

test_claim_is_claimed_returns_true_when_labeled() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123
    mock_issue_add_label 123 "wiggum:server:test-server-1"

    if claim_is_claimed 123; then
        assert_equals "0" "0" "claim_is_claimed should return 0 for claimed issue"
    else
        assert_equals "0" "1" "claim_is_claimed should return 0 for claimed issue"
    fi
    teardown
}

test_claim_is_claimed_returns_false_when_not_labeled() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123

    if claim_is_claimed 123; then
        assert_equals "1" "0" "claim_is_claimed should return 1 for unclaimed issue"
    else
        assert_equals "1" "1" "claim_is_claimed should return 1 for unclaimed issue"
    fi
    teardown
}

test_claim_verify_ownership_returns_true_for_owned() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123
    mock_issue_add_label 123 "wiggum:server:test-server-1"

    if claim_verify_ownership 123 "test-server-1"; then
        assert_equals "0" "0" "claim_verify_ownership should return 0 when we own it"
    else
        assert_equals "0" "1" "claim_verify_ownership should return 0 when we own it"
    fi
    teardown
}

test_claim_verify_ownership_returns_false_for_other_server() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123
    mock_issue_add_label 123 "wiggum:server:other-server"

    if claim_verify_ownership 123 "test-server-1"; then
        assert_equals "1" "0" "claim_verify_ownership should return 1 for other server"
    else
        assert_equals "1" "1" "claim_verify_ownership should return 1 for other server"
    fi
    teardown
}

test_claim_get_heartbeat_time_extracts_timestamp() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123
    mock_issue_add_heartbeat 123 "test-server-1" "2026-02-08T12:00:00+00:00"

    local heartbeat_time
    heartbeat_time=$(claim_get_heartbeat_time 123)

    # Should return a positive epoch timestamp
    if [ "$heartbeat_time" -gt 0 ] 2>/dev/null; then
        assert_equals "0" "0" "claim_get_heartbeat_time should return epoch timestamp"
    else
        assert_equals "0" "1" "claim_get_heartbeat_time should return epoch timestamp (got: $heartbeat_time)"
    fi
    teardown
}

test_claim_get_heartbeat_time_returns_zero_when_no_heartbeat() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123

    local heartbeat_time
    heartbeat_time=$(claim_get_heartbeat_time 123)
    assert_equals "0" "$heartbeat_time" "claim_get_heartbeat_time should return 0 when no heartbeat"
    teardown
}

test_claim_task_adds_assignee_and_label() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    mkdir -p "$TEST_DIR/ralph/server"

    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123

    # Override sleep to speed up test
    sleep() { :; }
    export -f sleep

    if claim_task 123 "test-server-1" "$TEST_DIR/ralph"; then
        # Check label was added
        local labels
        labels=$(cat "$MOCK_GH_DATA_DIR/issue-123-labels.txt")
        if echo "$labels" | grep -q "wiggum:server:test-server-1"; then
            assert_equals "0" "0" "claim_task should add server label"
        else
            assert_equals "0" "1" "claim_task should add server label (labels: $labels)"
        fi
    else
        assert_equals "0" "1" "claim_task should succeed"
    fi
    teardown
}

test_claim_release_task_removes_label_and_assignee() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/gh-error.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    mkdir -p "$TEST_DIR/ralph/server"

    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

    mock_issue_init 123
    mock_issue_add_label 123 "wiggum:server:test-server-1"
    echo "testuser" > "$MOCK_GH_DATA_DIR/issue-123-assignees.txt"

    if claim_release_task 123 "test-server-1" "$TEST_DIR/ralph" "test release"; then
        # Check label was removed
        local labels
        labels=$(cat "$MOCK_GH_DATA_DIR/issue-123-labels.txt")
        if echo "$labels" | grep -q "wiggum:server:test-server-1"; then
            assert_equals "1" "0" "claim_release_task should remove server label"
        else
            assert_equals "1" "1" "claim_release_task should remove server label"
        fi
    else
        assert_equals "0" "1" "claim_release_task should succeed"
    fi
    teardown
}

# =============================================================================
# orphan-recovery.sh Tests
# =============================================================================

test_orphan_recover_task_removes_labels_and_assignees() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"
    # Need to source task-source-github for label constants
    export WIGGUM_TASK_SOURCE_MODE=local
    source "$WIGGUM_HOME/lib/tasks/task-source-github.sh" 2>/dev/null || true
    source "$WIGGUM_HOME/lib/distributed/orphan-recovery.sh"

    mock_issue_init 123
    mock_issue_add_label 123 "wiggum:server:stale-server"
    mock_issue_add_label 123 "wiggum:in-progress"
    echo "testuser" > "$MOCK_GH_DATA_DIR/issue-123-assignees.txt"
    mock_issue_add_heartbeat 123 "stale-server" "2026-01-01T12:00:00+00:00"

    if orphan_recover_task 123 "stale-server" "$TEST_DIR/ralph"; then
        # Check server label was removed
        local labels
        labels=$(cat "$MOCK_GH_DATA_DIR/issue-123-labels.txt")
        if echo "$labels" | grep -q "wiggum:server:stale-server"; then
            assert_equals "1" "0" "orphan_recover_task should remove server label"
        else
            assert_equals "1" "1" "orphan_recover_task should remove server label"
        fi
    else
        assert_equals "0" "1" "orphan_recover_task should succeed"
    fi
    teardown
}

test_orphan_get_status_returns_json() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"
    source "$WIGGUM_HOME/lib/distributed/orphan-recovery.sh"

    local status
    status=$(orphan_get_status "$TEST_DIR/ralph" 600)

    # Should be valid JSON with expected fields
    local stale_count
    stale_count=$(echo "$status" | jq -r '.stale_count')
    assert_equals "0" "$stale_count" "orphan_get_status should return JSON with stale_count"
    teardown
}

# =============================================================================
# scheduler-integration.sh Tests
# =============================================================================

test_scheduler_claim_task_returns_success_in_local_mode() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    export WIGGUM_TASK_SOURCE_MODE=local
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"
    source "$WIGGUM_HOME/lib/distributed/heartbeat.sh"
    source "$WIGGUM_HOME/lib/distributed/orphan-recovery.sh"
    source "$WIGGUM_HOME/lib/distributed/scheduler-integration.sh"

    if scheduler_claim_task "TASK-001"; then
        assert_equals "0" "0" "scheduler_claim_task should succeed in local mode"
    else
        assert_equals "0" "1" "scheduler_claim_task should succeed in local mode"
    fi
    teardown
}

test_scheduler_release_task_returns_success_in_local_mode() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    export WIGGUM_TASK_SOURCE_MODE=local
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"
    source "$WIGGUM_HOME/lib/distributed/heartbeat.sh"
    source "$WIGGUM_HOME/lib/distributed/orphan-recovery.sh"
    source "$WIGGUM_HOME/lib/distributed/scheduler-integration.sh"

    if scheduler_release_task "TASK-001"; then
        assert_equals "0" "0" "scheduler_release_task should succeed in local mode"
    else
        assert_equals "0" "1" "scheduler_release_task should succeed in local mode"
    fi
    teardown
}

test_scheduler_get_distributed_status_returns_json() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    export WIGGUM_TASK_SOURCE_MODE=local
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"
    source "$WIGGUM_HOME/lib/distributed/heartbeat.sh"
    source "$WIGGUM_HOME/lib/distributed/orphan-recovery.sh"
    source "$WIGGUM_HOME/lib/distributed/scheduler-integration.sh"

    local status
    status=$(scheduler_get_distributed_status)

    # Should be valid JSON with mode field
    local mode
    mode=$(echo "$status" | jq -r '.mode')
    assert_equals "local" "$mode" "scheduler_get_distributed_status should return JSON with mode=local"
    teardown
}

test_scheduler_verify_ownership_returns_success_in_local_mode() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    export WIGGUM_TASK_SOURCE_MODE=local
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"
    source "$WIGGUM_HOME/lib/distributed/heartbeat.sh"
    source "$WIGGUM_HOME/lib/distributed/orphan-recovery.sh"
    source "$WIGGUM_HOME/lib/distributed/scheduler-integration.sh"

    if scheduler_verify_ownership "TASK-001"; then
        assert_equals "0" "0" "scheduler_verify_ownership should succeed in local mode"
    else
        assert_equals "0" "1" "scheduler_verify_ownership should succeed in local mode"
    fi
    teardown
}

# =============================================================================
# server-identity.sh Tests
# =============================================================================

test_server_identity_generate_returns_valid_format() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    local server_id
    server_id=$(server_identity_generate)

    # Should match format: hostname-random
    if [[ "$server_id" =~ ^[a-z0-9-]+-[a-f0-9]+$ ]]; then
        assert_equals "0" "0" "server_identity_generate should return valid format"
    else
        assert_equals "0" "1" "server_identity_generate should return valid format (got: $server_id)"
    fi
    teardown
}

test_server_identity_get_or_create_persists_identity() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph"

    local first_id second_id
    first_id=$(server_identity_get_or_create "$TEST_DIR/ralph")
    second_id=$(server_identity_get_or_create "$TEST_DIR/ralph")

    assert_equals "$first_id" "$second_id" "server_identity_get_or_create should return same ID on second call"
    teardown
}

test_server_identity_get_returns_empty_when_none_exists() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph"

    local server_id
    server_id=$(server_identity_get "$TEST_DIR/ralph")
    assert_equals "" "$server_id" "server_identity_get should return empty when no identity exists"
    teardown
}

test_server_identity_reset_generates_new_id() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph"

    local first_id second_id
    first_id=$(server_identity_get_or_create "$TEST_DIR/ralph")
    second_id=$(server_identity_reset "$TEST_DIR/ralph")

    assert_not_equals "$first_id" "$second_id" "server_identity_reset should generate new ID"
    teardown
}

test_server_config_load_sets_defaults() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    server_config_load "$TEST_DIR/ralph"

    # Check defaults were set
    assert_equals "180" "$SERVER_HEARTBEAT_INTERVAL" "server_config_load should set default heartbeat interval"
    assert_equals "300" "$SERVER_SYNC_INTERVAL" "server_config_load should set default sync interval"
    assert_equals "600" "$SERVER_STALE_THRESHOLD" "server_config_load should set default stale threshold"
    assert_equals "4" "$SERVER_MAX_CONCURRENT" "server_config_load should set default max concurrent"
    teardown
}

test_server_claims_update_add_creates_entry() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    server_claims_update "$TEST_DIR/ralph" "TASK-001" "add"

    # Check claims file was created
    assert_file_exists "$TEST_DIR/ralph/server/claims.json" "Claims file should be created"

    # Check task was added
    local has_task
    has_task=$(jq -r '.tasks | has("TASK-001")' "$TEST_DIR/ralph/server/claims.json")
    assert_equals "true" "$has_task" "Task should be added to claims"
    teardown
}

test_server_claims_update_remove_deletes_entry() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    server_claims_update "$TEST_DIR/ralph" "TASK-001" "add"
    server_claims_update "$TEST_DIR/ralph" "TASK-001" "remove"

    # Check task was removed
    local has_task
    has_task=$(jq -r '.tasks | has("TASK-001")' "$TEST_DIR/ralph/server/claims.json")
    assert_equals "false" "$has_task" "Task should be removed from claims"
    teardown
}

test_server_claims_list_returns_task_ids() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    server_claims_update "$TEST_DIR/ralph" "TASK-001" "add"
    server_claims_update "$TEST_DIR/ralph" "TASK-002" "add"

    local claims
    claims=$(server_claims_list "$TEST_DIR/ralph" | sort)

    local expected
    expected=$(printf "TASK-001\nTASK-002")
    assert_equals "$expected" "$claims" "server_claims_list should return task IDs"
    teardown
}

test_server_claims_has_returns_true_for_claimed() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    server_claims_update "$TEST_DIR/ralph" "TASK-001" "add"

    if server_claims_has "$TEST_DIR/ralph" "TASK-001"; then
        assert_equals "0" "0" "server_claims_has should return true for claimed task"
    else
        assert_equals "0" "1" "server_claims_has should return true for claimed task"
    fi
    teardown
}

test_server_claims_has_returns_false_for_unclaimed() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    server_claims_update "$TEST_DIR/ralph" "TASK-001" "add"

    if server_claims_has "$TEST_DIR/ralph" "TASK-002"; then
        assert_equals "1" "0" "server_claims_has should return false for unclaimed task"
    else
        assert_equals "1" "1" "server_claims_has should return false for unclaimed task"
    fi
    teardown
}

test_server_heartbeat_log_appends_entry() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    # Create identity first
    server_identity_get_or_create "$TEST_DIR/ralph" > /dev/null

    server_heartbeat_log "$TEST_DIR/ralph" "TASK-001" "claim"

    # Check log file was created
    assert_file_exists "$TEST_DIR/ralph/server/heartbeat.log" "Heartbeat log should be created"

    # Check entry was added
    local log_content
    log_content=$(cat "$TEST_DIR/ralph/server/heartbeat.log")
    if echo "$log_content" | grep -q "TASK-001.*claim"; then
        assert_equals "0" "0" "Heartbeat log should contain entry"
    else
        assert_equals "0" "1" "Heartbeat log should contain entry (got: $log_content)"
    fi
    teardown
}

test_server_heartbeat_log_rejects_invalid_task_id() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    # Create identity first
    server_identity_get_or_create "$TEST_DIR/ralph" > /dev/null

    # Try to log with invalid task ID (injection attempt)
    if server_heartbeat_log "$TEST_DIR/ralph" "TASK-001|malicious" "claim"; then
        assert_equals "1" "0" "server_heartbeat_log should reject invalid task ID"
    else
        assert_equals "1" "1" "server_heartbeat_log should reject invalid task ID"
    fi
    teardown
}

test_server_heartbeat_log_rejects_invalid_action() {
    setup
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/atomic-write.sh"
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    mkdir -p "$TEST_DIR/ralph/server"

    # Create identity first
    server_identity_get_or_create "$TEST_DIR/ralph" > /dev/null

    # Try to log with invalid action (injection attempt)
    if server_heartbeat_log "$TEST_DIR/ralph" "TASK-001" "claim|malicious"; then
        assert_equals "1" "0" "server_heartbeat_log should reject invalid action"
    else
        assert_equals "1" "1" "server_heartbeat_log should reject invalid action"
    fi
    teardown
}

# =============================================================================
# Run All Tests
# =============================================================================

run_test test_claim_get_owner_returns_server_id
run_test test_claim_get_owner_returns_empty_when_no_server
run_test test_claim_is_claimed_returns_true_when_labeled
run_test test_claim_is_claimed_returns_false_when_not_labeled
run_test test_claim_verify_ownership_returns_true_for_owned
run_test test_claim_verify_ownership_returns_false_for_other_server
run_test test_claim_get_heartbeat_time_extracts_timestamp
run_test test_claim_get_heartbeat_time_returns_zero_when_no_heartbeat
run_test test_claim_task_adds_assignee_and_label
run_test test_claim_release_task_removes_label_and_assignee

run_test test_orphan_recover_task_removes_labels_and_assignees
run_test test_orphan_get_status_returns_json

run_test test_scheduler_claim_task_returns_success_in_local_mode
run_test test_scheduler_release_task_returns_success_in_local_mode
run_test test_scheduler_get_distributed_status_returns_json
run_test test_scheduler_verify_ownership_returns_success_in_local_mode

run_test test_server_identity_generate_returns_valid_format
run_test test_server_identity_get_or_create_persists_identity
run_test test_server_identity_get_returns_empty_when_none_exists
run_test test_server_identity_reset_generates_new_id
run_test test_server_config_load_sets_defaults
run_test test_server_claims_update_add_creates_entry
run_test test_server_claims_update_remove_deletes_entry
run_test test_server_claims_list_returns_task_ids
run_test test_server_claims_has_returns_true_for_claimed
run_test test_server_claims_has_returns_false_for_unclaimed
run_test test_server_heartbeat_log_appends_entry
run_test test_server_heartbeat_log_rejects_invalid_task_id
run_test test_server_heartbeat_log_rejects_invalid_action

print_test_summary
exit_with_test_result
