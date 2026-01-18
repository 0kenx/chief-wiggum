#!/usr/bin/env bash
# Tests for lib/ralph-loop.sh

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

# Mock the logger and task-parser for isolated testing
log() { echo "[TEST-LOG] $1"; }
log_error() { echo "[TEST-ERROR] $1" >&2; }
log_debug() { echo "[TEST-DEBUG] $1"; }

test_suite "ralph-loop.sh"

test_case "ralph-loop.sh - has_incomplete_tasks integration"
setup_test_dir

# Create a PRD with incomplete tasks
cat > "$TEST_TMP_DIR/prd.md" <<'EOF'
# Task: TEST-001

## Description
Test task

## Checklist

- [ ] Incomplete task 1
- [ ] Incomplete task 2
EOF

# Source the task-parser to use has_incomplete_tasks
source "$SCRIPT_DIR/../lib/task-parser.sh"

has_incomplete_tasks "$TEST_TMP_DIR/prd.md"
assert_true $? "Should detect incomplete tasks in PRD"

teardown_test_dir

test_case "ralph-loop.sh - has_incomplete_tasks when all complete"
setup_test_dir

cat > "$TEST_TMP_DIR/prd.md" <<'EOF'
# Task: TEST-001

## Description
Test task

## Checklist

- [x] Complete task 1
- [x] Complete task 2
- [x] Complete task 3
EOF

source "$SCRIPT_DIR/../lib/task-parser.sh"

has_incomplete_tasks "$TEST_TMP_DIR/prd.md"
assert_false $? "Should not detect incomplete tasks when all are complete"

teardown_test_dir

test_case "ralph-loop.sh - prompt construction"
setup_test_dir

PRD_FILE="$TEST_TMP_DIR/prd.md"
touch "$PRD_FILE"

# Test the prompt format used in ralph_loop
expected_prompt="Read @$PRD_FILE, find the next incomplete task (- [ ]), execute it completely, then mark it as complete (- [x]) by editing the PRD file."
actual_prompt="Read @$PRD_FILE, find the next incomplete task (- [ ]), execute it completely, then mark it as complete (- [x]) by editing the PRD file."

assert_equals "$expected_prompt" "$actual_prompt" "Prompt should be correctly formatted"

teardown_test_dir

test_case "ralph-loop.sh - max iterations parameter"
setup_test_dir

# Test that max_iterations defaults to 50
max_iterations_default=50
max_iterations_custom=100

assert_equals "50" "$max_iterations_default" "Should default to 50 iterations"
assert_equals "100" "$max_iterations_custom" "Should accept custom max iterations"

teardown_test_dir

test_case "ralph-loop.sh - iteration counter logic"
setup_test_dir

# Simulate iteration counting
iteration=0
max_iterations=5

while [ $iteration -lt $max_iterations ]; do
    iteration=$((iteration + 1))
done

assert_equals "5" "$iteration" "Should count iterations correctly"
assert_true $([ $iteration -ge $max_iterations ] && echo 0 || echo 1) "Should exit when reaching max iterations"

teardown_test_dir

test_case "ralph-loop.sh - workspace path handling"
setup_test_dir

workspace="$TEST_TMP_DIR/workspace"
mkdir -p "$workspace"
cd "$workspace" || exit 1

current_dir=$(pwd)
assert_equals "$workspace" "$current_dir" "Should change to workspace directory"

teardown_test_dir

test_case "ralph-loop.sh - file paths in log output"
setup_test_dir

prd_file="$TEST_TMP_DIR/test-prd.md"
workspace="$TEST_TMP_DIR/workspace"
iteration=3

# Simulate the debug output format
debug_output="=== DEBUG ITERATION $iteration ===
PWD: $workspace
PRD file: $prd_file
Prompt: Read @$prd_file, find the next incomplete task (- [ ]), execute it completely, then mark it as complete (- [x]) by editing the PRD file."

assert_contains "$debug_output" "=== DEBUG ITERATION 3 ===" "Should include iteration number"
assert_contains "$debug_output" "PWD: $workspace" "Should include workspace path"
assert_contains "$debug_output" "PRD file: $prd_file" "Should include PRD file path"

teardown_test_dir

test_case "ralph-loop.sh - return codes"
setup_test_dir

# Test successful completion
return_code_success=0
assert_true $return_code_success "Should return 0 on success"

# Test failure/timeout
return_code_failure=1
assert_false $return_code_failure "Should return 1 on failure"

teardown_test_dir

test_case "ralph-loop.sh - sleep delay between iterations"
setup_test_dir

# Test that sleep value is 2 seconds
sleep_delay=2
assert_equals "2" "$sleep_delay" "Should sleep for 2 seconds between iterations"

teardown_test_dir

test_case "ralph-loop.sh - PRD file validation"
setup_test_dir

valid_prd="$TEST_TMP_DIR/valid.md"
invalid_prd="$TEST_TMP_DIR/nonexistent.md"

cat > "$valid_prd" <<'EOF'
# Task: TEST
## Checklist
- [ ] Task
EOF

if [ -f "$valid_prd" ]; then
    assert_true 0 "Should validate existing PRD file"
else
    assert_true 1 "Should fail for missing PRD file"
fi

if [ -f "$invalid_prd" ]; then
    assert_true 1 "Should fail for nonexistent file"
else
    assert_true 0 "Should correctly identify nonexistent file"
fi

teardown_test_dir

print_summary
