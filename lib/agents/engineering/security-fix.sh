#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: security-fix
# AGENT_DESCRIPTION: Security fix agent that addresses vulnerabilities found by
#   security-audit. Uses ralph loop pattern to iteratively fix security issues.
#   Reads findings from security-report.md, makes code changes, and tracks
#   progress in fix-status.md. Prioritizes CRITICAL > HIGH > MEDIUM fixes.
# REQUIRED_PATHS:
#   - reports/security-report.md : Security audit report containing findings to fix
#   - workspace                  : Directory containing the code to modify
# OUTPUT_FILES:
#   - reports/fix-status.md      : Status tracking file for addressed findings
#   - results/fix-result.json    : Contains PASS, FIX, or FAIL
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "engineering.security-fix" "Security fix agent that addresses vulnerabilities found by security-audit"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Pre-run hook: locate upstream security-audit report
agent_on_ready() {
    local worker_dir="$1"
    _SECURITY_REPORT_FILE=$(agent_find_latest_report "$worker_dir" "security-audit")
    if [ -z "$_SECURITY_REPORT_FILE" ] || [ ! -f "$_SECURITY_REPORT_FILE" ]; then
        log_error "No security-audit report found. Run security-audit agent first."
        return 1
    fi
    return 0
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Global for result tracking
FIX_RESULT="UNKNOWN"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    local max_iterations="${WIGGUM_SECURITY_FIX_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-15}}"
    local max_turns="${WIGGUM_SECURITY_FIX_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-50}}"

    local workspace="$worker_dir/workspace"
    local report_file="${_SECURITY_REPORT_FILE:-}"
    local status_file="$worker_dir/reports/fix-status.md"

    # Verify workspace exists
    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        FIX_RESULT="FAIL"
        agent_write_result "$worker_dir" "failure" 1 '{"gate_result":"FAIL"}'
        return 1
    fi

    # Verify security report exists (should be set by agent_on_ready)
    if [ -z "$report_file" ] || [ ! -f "$report_file" ]; then
        log_error "Security report not found"
        log_error "Run security-audit agent first"
        FIX_RESULT="FAIL"
        agent_write_result "$worker_dir" "failure" 1 '{"gate_result":"FAIL"}'
        return 1
    fi

    # Check if there are any findings to fix
    if ! grep -qE '^### (CRITICAL|HIGH|MEDIUM)' "$report_file" 2>/dev/null; then
        log "No CRITICAL/HIGH/MEDIUM findings in security report - nothing to fix"
        FIX_RESULT="PASS"
        agent_write_result "$worker_dir" "success" 0 '{"gate_result":"PASS"}'
        echo "# Security Fix Status

**Status:** No fixes needed

No CRITICAL, HIGH, or MEDIUM security findings were present in the report.
" > "$status_file"
        return 0
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Initialize status tracking
    _init_fix_status "$report_file" "$status_file"

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"
    _FIX_REPORT_FILE="$report_file"
    _FIX_STATUS_FILE="$status_file"

    # Create stable symlink so prompts can reference a known report path
    ln -sf "$(basename "$report_file")" "$worker_dir/reports/security-report.md"

    log "Starting security fix loop (max $max_iterations iterations, $max_turns turns/session)"

    # Run the fix loop
    run_ralph_loop \
        "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_fix_user_prompt" \
        "_fix_completion_check" \
        "$max_iterations" \
        "$max_turns" \
        "$worker_dir" \
        "fix"

    local loop_result=$?

    # Determine final result
    _determine_fix_result "$status_file" "$worker_dir"

    if [ "$FIX_RESULT" = "PASS" ]; then
        log "All security issues fixed successfully"
    elif [ "$FIX_RESULT" = "FIX" ]; then
        log_warn "Some security issues could not be fixed"
    else
        log_error "Security fix failed"
    fi

    return $loop_result
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << EOF
SECURITY FIX AGENT:

You fix security vulnerabilities identified by the security audit.

WORKSPACE: $workspace
REPORT: ../reports/security-report.md (read-only - contains findings to fix)
STATUS: ../reports/fix-status.md (update as you fix)

## Fix Philosophy

* UNDERSTAND THE VULNERABILITY - Read the finding carefully before fixing
* MINIMAL CHANGES - Fix the security issue without unnecessary refactoring
* VERIFY THE FIX - Ensure your change actually addresses the vulnerability
* DON'T BREAK FUNCTIONALITY - Security fixes should maintain existing behavior
* FOLLOW PATTERNS - Match existing code style and security patterns in the codebase

## Priority Order

1. CRITICAL - Fix these first (immediate exploitation risk)
2. HIGH - Fix next (serious vulnerabilities)
3. MEDIUM - Fix last (limited impact issues)

## Rules

* Read the vulnerability description and evidence carefully
* Make targeted fixes - don't over-engineer
* Update status file AFTER each successful fix
* Stay within workspace directory
* If a fix requires architectural changes, mark as [*] with explanation

## Git Restrictions (CRITICAL)

The workspace contains uncommitted work from other agents. You MUST NOT destroy it.

**FORBIDDEN git commands (will terminate your session):**
- \`git checkout -- <file>\` - DESTROYS uncommitted file changes
- \`git checkout .\` - DESTROYS all uncommitted changes
- \`git stash\` - Hides uncommitted changes
- \`git reset --hard\` - DESTROYS uncommitted changes
- \`git clean\` - DELETES untracked files
- \`git restore\` - DESTROYS uncommitted changes
- \`git commit\` - Commits are handled by the orchestrator
- \`git add\` - Staging is handled by the orchestrator

**ALLOWED git commands (read-only):**
- \`git status\`, \`git diff\`, \`git log\`, \`git show\`
EOF
}

# Get context files section for user prompt
_get_context_section() {
    local worker_dir
    worker_dir=$(agent_get_worker_dir)

    cat << 'EOF'
## Context

Before fixing, understand what was implemented:

EOF

    # Check for PRD
    if [ -f "$worker_dir/prd.md" ]; then
        cat << 'EOF'
1. **Read the PRD** (@../prd.md) - Understand the original requirements
EOF
    fi

    # Check for implementation summary
    if [ -f "$worker_dir/summaries/summary.txt" ]; then
        cat << 'EOF'
2. **Read the Implementation Summary** (@../summaries/summary.txt) - Understand what was built and how
EOF
    fi

    echo ""
}

# User prompt callback
_fix_user_prompt() {
    local iteration="$1"
    local output_dir="$2"

    # Include context section first
    _get_context_section

    # Always include the initial prompt to ensure full context after summarization
    cat << 'EOF'
SECURITY FIX TASK:

Fix security vulnerabilities from the audit report.

## Process

1. **Read the report**: @../reports/security-report.md - understand the vulnerabilities
2. **Check status**: @../reports/fix-status.md - skip [x] items, fix [ ] items
3. **For each pending finding** (in priority order: CRITICAL → HIGH → MEDIUM):
   - Read the vulnerability details (location, evidence, remediation)
   - Navigate to the affected file and line
   - Implement the fix following the suggested remediation
   - Verify the fix addresses the vulnerability
   - Update status: `- [ ] SEC-XXX` → `- [x] SEC-XXX: <what you fixed>`
4. **Repeat** until no [ ] items remain

## Common Fixes

| Vulnerability | Typical Fix |
|---------------|-------------|
| SQL Injection | Use parameterized queries / prepared statements |
| Command Injection | Use subprocess with array args, avoid shell=True |
| XSS | Escape output, use safe templating |
| Hardcoded Secrets | Move to environment variables / secret manager |
| Path Traversal | Validate and sanitize file paths |
| Weak Crypto | Use strong algorithms (AES-256, SHA-256+) |
| Insecure Deserialization | Use safe loaders, validate input |

## Status File Format

```markdown
- [x] SEC-001: Replaced string concatenation with parameterized query
- [*] SEC-002: Cannot fix - requires database schema change
- [ ] SEC-003  ← Still needs work
```

Markers:
* `[x]` = Fixed
* `[*]` = Cannot fix (with explanation)
* `[ ]` = Pending

## Rules

* ONE finding at a time - fix completely before moving on
* Update status IMMEDIATELY after each fix
* CRITICAL and HIGH findings must be fixed; MEDIUM is best-effort
* If you can't fix something, mark [*] with clear explanation
* Stay within workspace directory

## Output Format

When all fixes are complete, provide:

<summary>
## Security Fixes Applied

| ID | Severity | File | Fix Applied |
|----|----------|------|-------------|
| SEC-001 | CRITICAL | path/file.py:42 | Parameterized SQL query |

## Remaining Issues
(List any [*] items that couldn't be fixed)

## Verification
- [ ] All CRITICAL issues addressed
- [ ] All HIGH issues addressed
- [ ] MEDIUM issues addressed or documented
</summary>

<result>PASS</result>
OR
<result>FIX</result>
OR
<result>FAIL</result>

The <result> tag MUST be exactly: PASS, FIX, or FAIL.
EOF

    # Add context from previous iterations if available
    if [ "$iteration" -gt 0 ]; then
        local prev_iter=$((iteration - 1))
        if [ -f "$output_dir/summaries/fix-$prev_iter-summary.txt" ]; then
            cat << CONTEXT_EOF

CONTINUATION CONTEXT (Iteration $iteration):

To understand what has already been fixed:
- Read @../summaries/fix-$prev_iter-summary.txt for context on previous fixes
- Check @../reports/fix-status.md to see which findings are already addressed
- Do NOT repeat work that was already completed
CONTEXT_EOF
        fi
    fi
}

# Completion check callback
_fix_completion_check() {
    local status_file="$_FIX_STATUS_FILE"

    # If status file doesn't exist, not complete
    if [ ! -f "$status_file" ]; then
        return 1
    fi

    # Check if any pending items remain (lines starting with "- [ ]")
    if grep -q '^\- \[ \]' "$status_file" 2>/dev/null; then
        return 1  # Still has pending items
    fi

    return 0  # All items checked off or marked as unable to fix
}

# Initialize fix status tracking file from security report
_init_fix_status() {
    local report_file="$1"
    local status_file="$2"

    {
        echo "# Security Fix Status"
        echo ""
        echo "**Generated:** $(date -Iseconds)"
        echo "**Report:** security-report.md"
        echo ""
        echo "## Findings to Fix"
        echo ""
        echo "Mark findings as fixed by changing \`[ ]\` to \`[x]\` and adding a brief description."
        echo "Mark findings that cannot be fixed with \`[*]\` and explain why."
        echo ""
        echo "### CRITICAL"
        echo ""
    } > "$status_file"

    # Extract findings by severity
    {
        _extract_findings_by_severity "$report_file" "CRITICAL"

        echo ""
        echo "### HIGH"
        echo ""

        _extract_findings_by_severity "$report_file" "HIGH"

        echo ""
        echo "### MEDIUM"
        echo ""

        _extract_findings_by_severity "$report_file" "MEDIUM"
    } >> "$status_file"

    local total_count
    total_count=$(grep -c '^\- \[ \]' "$status_file" 2>/dev/null || echo "0")
    log "Initialized status file with $total_count findings to fix"
}

# Extract findings by severity from report
_extract_findings_by_severity() {
    local report_file="$1"
    local severity="$2"

    # Look for finding IDs like [SEC-001] under the severity section
    local in_section=false
    while IFS= read -r line; do
        if [[ "$line" =~ ^###\ $severity ]]; then
            in_section=true
            continue
        elif [[ "$line" =~ ^###\  ]] && [ "$in_section" = true ]; then
            # Hit next section
            break
        fi

        if [ "$in_section" = true ]; then
            # Extract finding ID from lines like "- **[SEC-001]**" or "**[SEC-001]**"
            if [[ "$line" =~ \[SEC-([0-9]+)\] ]]; then
                local finding_id="SEC-${BASH_REMATCH[1]}"
                echo "- [ ] $finding_id"
            fi
        fi
    done < "$report_file"
}

# Determine final fix result
_determine_fix_result() {
    local status_file="$1"
    local worker_dir="$2"

    FIX_RESULT="UNKNOWN"

    if [ ! -f "$status_file" ]; then
        FIX_RESULT="FAIL"
        agent_write_result "$worker_dir" "failure" 1 '{"gate_result":"FAIL"}'
        return
    fi

    local pending_count fixed_count unfixable_count
    pending_count=$(grep -c '^\- \[ \]' "$status_file" 2>/dev/null || echo "0")
    fixed_count=$(grep -c '^\- \[x\]' "$status_file" 2>/dev/null || echo "0")
    unfixable_count=$(grep -c '^\- \[\*\]' "$status_file" 2>/dev/null || echo "0")

    if [ "$pending_count" -eq 0 ] && [ "$unfixable_count" -eq 0 ]; then
        FIX_RESULT="PASS"
    elif [ "$pending_count" -eq 0 ] && [ "$unfixable_count" -gt 0 ]; then
        FIX_RESULT="FIX"
    elif [ "$fixed_count" -gt 0 ]; then
        FIX_RESULT="FIX"
    else
        FIX_RESULT="FAIL"
    fi

    local status="failure"
    [ "$FIX_RESULT" = "PASS" ] && status="success"
    [ "$FIX_RESULT" = "FIX" ] && status="partial"
    local gate_json
    gate_json=$(printf '{"gate_result":"%s","fixed":%d,"unfixable":%d,"pending":%d}' \
        "$FIX_RESULT" "$fixed_count" "$unfixable_count" "$pending_count")
    agent_write_result "$worker_dir" "$status" "$([ "$FIX_RESULT" = "PASS" ] && echo 0 || echo 1)" "$gate_json"

    log "Fix result: $FIX_RESULT (fixed: $fixed_count, unfixable: $unfixable_count, pending: $pending_count)"
}

# Check fix result from a worker directory (utility for callers)
# Returns: 0 if PASS, 1 if FIX, 2 if FAIL/UNKNOWN
check_fix_result() {
    local worker_dir="$1"
    local result
    result=$(agent_read_subagent_result "$worker_dir" "security-fix")

    case "$result" in
        PASS) return 0 ;;
        FIX) return 1 ;;
        *) return 2 ;;
    esac
}
