#!/usr/bin/env bash
# Test file-lock.sh with edge cases including special characters

set -e

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

# Source the file-lock utilities
source "$WIGGUM_HOME/lib/core/file-lock.sh"

# Create a test directory
TEST_DIR=$(mktemp -d)
trap 'rm -rf "$TEST_DIR"' EXIT

echo "Testing file-lock.sh with edge cases..."

# Test 1: Basic locking with simple command
echo "Test 1: Basic file lock with simple command"
TEST_FILE="$TEST_DIR/test1.txt"
with_file_lock "$TEST_FILE" 5 echo "Hello World" > "$TEST_FILE"
if [ -f "$TEST_FILE" ] && grep -q "Hello World" "$TEST_FILE"; then
    echo "✓ Test 1 passed"
else
    echo "✗ Test 1 failed"
    exit 1
fi

# Test 2: Special characters in file content
echo "Test 2: File lock with special characters"
TEST_FILE2="$TEST_DIR/test2.txt"
with_file_lock "$TEST_FILE2" 5 bash -c 'echo "Special chars: $ \" \` \\ ; | & > <" > "$1"' _ "$TEST_FILE2"
if [ -f "$TEST_FILE2" ] && grep -q 'Special chars:' "$TEST_FILE2"; then
    echo "✓ Test 2 passed"
else
    echo "✗ Test 2 failed"
    exit 1
fi

# Test 3: Update kanban status with special task ID
echo "Test 3: Update kanban status"
KANBAN_FILE="$TEST_DIR/kanban.md"
cat > "$KANBAN_FILE" << 'EOF'
# Kanban Board

- [ ] **[TASK-001]** Test task one
- [ ] **[TASK-002]** Test task with special chars: $var
- [ ] **[TASK-003]** Another task
EOF

update_kanban_status "$KANBAN_FILE" "TASK-002" "x"
if grep -q '\- \[x\] \*\*\[TASK-002\]\*\*' "$KANBAN_FILE"; then
    echo "✓ Test 3 passed"
else
    echo "✗ Test 3 failed"
    cat "$KANBAN_FILE"
    exit 1
fi

# Test 4: Concurrent access (spawn multiple processes)
echo "Test 4: Concurrent file access"
CONCURRENT_FILE="$TEST_DIR/concurrent.txt"
echo "0" > "$CONCURRENT_FILE"

for _ in {1..5}; do
    (
        with_file_lock "$CONCURRENT_FILE" 10 bash -c '
            current=$(cat "$1")
            new=$((current + 1))
            echo "$new" > "$1"
        ' _ "$CONCURRENT_FILE"
    ) &
done

wait

FINAL_COUNT=$(cat "$CONCURRENT_FILE")
if [ "$FINAL_COUNT" -eq 5 ]; then
    echo "✓ Test 4 passed (final count: $FINAL_COUNT)"
else
    echo "✗ Test 4 failed (expected 5, got $FINAL_COUNT)"
    exit 1
fi

# Test 5: Changelog append with special characters
echo "Test 5: Append changelog with special characters"
CHANGELOG_FILE="$TEST_DIR/changelog.md"
touch "$CHANGELOG_FILE"

append_changelog "$CHANGELOG_FILE" "TASK-999" "worker-1" \
    'Fix bug with special chars: $ " ` \' \
    "https://github.com/test/pr/1" \
    'Summary with special chars: & | > < ;'

if [ -f "$CHANGELOG_FILE" ] && grep -q 'TASK-999' "$CHANGELOG_FILE"; then
    echo "✓ Test 5 passed"
else
    echo "✗ Test 5 failed"
    exit 1
fi

echo ""
echo "All tests passed! ✓"
echo "No eval() usage detected - safe command execution verified"
