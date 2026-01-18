# Chief Wiggum Test Suite

Automated tests for the core functionality of Chief Wiggum.

## Test Structure

- `test-framework.sh` - Simple bash testing framework with assertions
- `test-task-parser.sh` - Tests for lib/task-parser.sh
- `test-worker.sh` - Tests for lib/worker.sh
- `test-ralph-loop.sh` - Tests for lib/ralph-loop.sh
- `test-edge-cases.sh` - Edge cases and integration tests
- `run-all-tests.sh` - Master test runner

## Running Tests

Run all tests:
```bash
bash tests/run-all-tests.sh
```

Run individual test suite:
```bash
bash tests/test-task-parser.sh
bash tests/test-worker.sh
bash tests/test-ralph-loop.sh
bash tests/test-edge-cases.sh
```

## Test Coverage

### task-parser.sh
- `has_incomplete_tasks()` - Detects incomplete tasks in PRD files
- `get_todo_tasks()` - Extracts task IDs from kanban TODO section
- `extract_task()` - Generates PRD from kanban task entry
- Edge cases: different task ID formats, empty files, malformed entries

### worker.sh
- Git worktree creation and cleanup
- Task completion marking in kanban
- Results directory management
- Environment variable handling

### ralph-loop.sh
- Iteration control and max iterations
- PRD file validation
- Prompt construction
- Workspace navigation
- Return codes

### Edge Cases and Integration
- Unicode and special characters in task descriptions
- Very long task descriptions
- Multiple dependencies
- Task ID length validation
- Malformed task entries
- Nested checkboxes
- Complete workflow integration
- Multiple task processing
- Concurrent access patterns
- Skills integration

## Test Statistics

Total test suites: 4
Total assertions: 75+
Coverage: Core functionality, edge cases, and integration scenarios

## Adding New Tests

1. Use the test framework's assertion functions:
   - `assert_equals` - Check equality
   - `assert_true` - Check boolean true
   - `assert_false` - Check boolean false
   - `assert_contains` - Check substring presence
   - `assert_not_contains` - Check substring absence
   - `assert_file_exists` - Check file existence

2. Use setup/teardown helpers:
   - `setup_test_dir` - Creates temporary test directory
   - `teardown_test_dir` - Cleans up test directory

3. Structure your test:
```bash
test_case "Description of what is being tested"
setup_test_dir

# Test code here
# Use assertions

teardown_test_dir
```

4. Add your test to `run-all-tests.sh` if creating a new suite
