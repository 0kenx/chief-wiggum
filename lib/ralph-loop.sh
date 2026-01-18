#!/usr/bin/env bash
# Ralph Wiggum Loop - Self-prompting execution pattern

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/task-parser.sh"
source "$SCRIPT_DIR/logger.sh"

ralph_loop() {
    local prd_file="$1"                    # Worker's PRD file (absolute path)
    local agent_file="$2"                  # Agent definition
    local workspace="$3"                   # Worker's git worktree
    local max_iterations="${4:-50}"
    local iteration=0

    log "Ralph loop starting for $prd_file"

    # Change to workspace BEFORE the loop
    cd "$workspace" || exit 1

    # Convert PRD file to relative path from workspace
    local prd_relative="../prd.md"

    while [ $iteration -lt $max_iterations ]; do
        # Exit if all tasks complete
        if ! has_incomplete_tasks "$prd_file"; then
            log "Worker completed all tasks in $prd_file"
            break
        fi

        # Build prompt using relative path to PRD
        local prompt="IMPORTANT: Your working directory is $workspace. Do NOT cd into, read, or modify files outside this directory. INSTRUCTIONS:Read @$prd_relative, find the next incomplete task (- [ ]), execute it completely within your working directory, then mark it as complete (- [x]) by editing the PRD file."

        log_debug "Iteration $iteration: Executing Claude Code"

        # Debug: show exact command
        {
            echo "=== DEBUG ITERATION $iteration ==="
            echo "PWD: $(pwd)"
            echo "PRD file (relative): $prd_relative"
            echo "Prompt: $prompt"
            echo "Command: claude --verbose --output-format stream-json --plugin-dir \"$WIGGUM_HOME/skills\" -p \"$prompt\""
            echo "=== RUNNING ==="
        } >> "../worker.log"

        # Run Claude with the prompt (already in workspace directory)
        # Load chief-wiggum skills for task completion and progress reporting
        # Workspace isolation is enforced via PreToolUse hooks
        claude --verbose --output-format stream-json --plugin-dir "$WIGGUM_HOME/skills" -p "$prompt" >> "../worker.log" 2>&1

        iteration=$((iteration + 1))
        sleep 2  # Prevent tight loop
    done

    if [ $iteration -ge $max_iterations ]; then
        log_error "Worker reached max iterations ($max_iterations) without completing all tasks"
        return 1
    fi

    log "Worker finished after $iteration iterations"
    return 0
}
