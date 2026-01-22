#!/usr/bin/env bash
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: security-audit
# AGENT_DESCRIPTION: Security vulnerability scanner agent that audits codebase
#   for security issues. Uses ralph loop pattern with summaries. Scans for
#   secrets, OWASP Top 10, injection patterns, and insecure coding practices.
#   Returns PASS/WARN/FAIL result based on finding severity.
# REQUIRED_PATHS:
#   - workspace : Directory containing the code to audit
# OUTPUT_FILES:
#   - security-report.md  : Detailed security findings
#   - security-result.txt : Contains PASS, WARN, or FAIL
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "security-audit" "Security vulnerability scanner that audits codebase for security issues"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "security-result.txt"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Global for result tracking
SECURITY_RESULT="UNKNOWN"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    local max_turns="${WIGGUM_SECURITY_AUDIT_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-60}}"
    local max_iterations="${WIGGUM_SECURITY_AUDIT_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-8}}"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        SECURITY_RESULT="UNKNOWN"
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Clean up old audit files before re-running
    rm -f "$worker_dir/security-result.txt" "$worker_dir/security-report.md"
    rm -f "$worker_dir/logs/audit-"*.log
    rm -f "$worker_dir/summaries/audit-"*.txt

    log "Running security audit..."

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    # Run audit loop
    run_ralph_loop "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_audit_user_prompt" \
        "_audit_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "audit"

    local agent_exit=$?

    # Parse result from the latest audit log
    _extract_audit_result "$worker_dir"

    if [ $agent_exit -eq 0 ]; then
        log "Security audit completed with result: $SECURITY_RESULT"
    else
        log_warn "Security audit had issues (exit: $agent_exit)"
    fi

    return $agent_exit
}

# User prompt callback for ralph loop
_audit_user_prompt() {
    local iteration="$1"
    local output_dir="$2"

    # Always include the initial prompt to ensure full context after summarization
    _get_user_prompt

    if [ "$iteration" -gt 0 ]; then
        # Add continuation context for subsequent iterations
        local prev_iter=$((iteration - 1))
        cat << CONTINUE_EOF

CONTINUATION CONTEXT (Iteration $iteration):

Your previous audit work is summarized in @../summaries/audit-$prev_iter-summary.txt.

Please continue your audit:
1. If you haven't completed all scan categories, continue from where you left off
2. If you found issues that need deeper investigation, investigate them now
3. When your audit is complete, provide the final <report> and <result> tags

Remember: The <result> tag must contain exactly PASS, WARN, or FAIL.
CONTINUE_EOF
    fi
}

# Completion check callback - returns 0 if audit is complete
_audit_completion_check() {
    # Check if any audit log contains a result tag
    local worker_dir
    worker_dir=$(agent_get_worker_dir)
    local latest_log
    latest_log=$(find "$worker_dir/logs" -maxdepth 1 -name "audit-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$latest_log" ] && [ -f "$latest_log" ]; then
        if grep -qP '<result>(PASS|WARN|FAIL)</result>' "$latest_log" 2>/dev/null; then
            return 0  # Complete
        fi
    fi

    return 1  # Not complete
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << EOF
SECURITY AUDITOR:

You scan code for security vulnerabilities. Your job is to find REAL issues, not theoretical ones.

WORKSPACE: $workspace

## Audit Philosophy

* HIGH CONFIDENCE ONLY - Only report issues you're confident are real vulnerabilities
* VERIFY BEFORE REPORTING - Check context; what looks dangerous might be safe
* EVIDENCE REQUIRED - Every finding needs concrete evidence (file, line, code snippet)
* SEVERITY MATTERS - Don't inflate severity; be accurate about real impact

## What Makes a Real Vulnerability

* It's actually exploitable (not just a pattern that COULD be dangerous)
* External input reaches the dangerous operation
* There's no sanitization/validation in between
* The impact is real (not just theoretical)

## Common False Positives to Avoid

* Hardcoded strings that aren't actually secrets (example values, test data)
* Internal-only code paths that can't receive external input
* Properly parameterized queries flagged as "SQL injection"
* Test files with intentionally insecure patterns
EOF
}

# User prompt
_get_user_prompt() {
    cat << 'EOF'
SECURITY AUDIT TASK:

Scan the codebase for security vulnerabilities.

## Priority Scan Areas

### 1. Secrets not excluded in .gitignore (CRITICAL)
* Hardcoded API keys, tokens, passwords in source code
* Private keys or certificates committed
* Database credentials in config files
* Cloud provider credentials (AWS/GCP/Azure)
* Files that should not be committed to source control

### 2. Injection Vulnerabilities (CRITICAL/HIGH)
* SQL injection - string concatenation with user input in queries
* Command injection - shell execution with unsanitized input
* XSS - unescaped user input in HTML output
* Path traversal - user input in file paths without validation

### 3. Authentication/Authorization (HIGH)
* Missing authentication on sensitive endpoints
* Broken access control (users accessing others' data)
* Weak session management

### 4. Insecure Patterns (MEDIUM)
* eval()/exec() with external input
* Unsafe deserialization (pickle, yaml.load without SafeLoader)
* Weak cryptography (MD5/SHA1 for security, ECB mode)
* Missing input validation at trust boundaries

### 5. CI/CD Pipeline Vulnerabilities (CRITICAL)
* Malicious code execution in CI/CD pipeline
* Unjustified access to CI/CD secrets or credentials

## Severity Guide

| Severity | Criteria | Examples |
|----------|----------|----------|
| CRITICAL | Immediate RCE or data breach possible | Hardcoded prod secrets, SQLi with user input |
| HIGH | Exploitable with some conditions | Auth bypass, command injection |
| MEDIUM | Limited impact or harder to exploit | Missing rate limiting, verbose errors |
| LOW | Defense-in-depth concerns | Missing security headers |

## Result Criteria

* **FAIL**: Any CRITICAL or HIGH findings
* **WARN**: MEDIUM findings only
* **PASS**: Only LOW/INFO or no findings

## Output Format

<report>

## Summary
[1-2 sentences: security posture assessment]

## Findings

### CRITICAL
- **[SEC-001]** [Name] - File:Line (if applicable)
  - **Issue**: [What's wrong]
  - **Evidence**: `[code snippet]`
  - **Fix**: [How to remediate]

### HIGH
(same format)

### MEDIUM
(same format)

### LOW
(same format)

(Omit empty severity sections)

## Coverage
Files scanned: N | Limitations: [any areas not fully assessed]

</report>

<result>PASS</result>
OR
<result>WARN</result>
OR
<result>FAIL</result>

The <result> tag MUST be exactly: PASS, WARN, or FAIL.
EOF
}

# Extract audit result from log files
_extract_audit_result() {
    local worker_dir="$1"

    SECURITY_RESULT="UNKNOWN"

    # Find the latest audit log (excluding summary logs)
    local log_file
    log_file=$(find "$worker_dir/logs" -maxdepth 1 -name "audit-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$log_file" ] && [ -f "$log_file" ]; then
        # Extract report content between <report> tags
        local report_path="$worker_dir/security-report.md"
        if grep -q '<report>' "$log_file"; then
            sed -n '/<report>/,/<\/report>/p' "$log_file" | sed '1d;$d' > "$report_path"
            log "Security report saved to security-report.md"
        fi

        # Extract result tag (PASS, WARN, or FAIL)
        SECURITY_RESULT=$(grep -oP '(?<=<result>)(PASS|WARN|FAIL)(?=</result>)' "$log_file" | head -1)
        if [ -z "$SECURITY_RESULT" ]; then
            SECURITY_RESULT="UNKNOWN"
        fi
    fi

    # Store result in standard location
    echo "$SECURITY_RESULT" > "$worker_dir/security-result.txt"
}

# Check security result from a worker directory (utility for callers)
# Returns: 0 if PASS, 1 if WARN, 2 if FAIL/UNKNOWN
check_security_result() {
    local worker_dir="$1"
    local result_file="$worker_dir/security-result.txt"

    if [ -f "$result_file" ]; then
        local result
        result=$(cat "$result_file")
        case "$result" in
            PASS)
                return 0
                ;;
            WARN)
                return 1
                ;;
            FAIL|UNKNOWN|*)
                return 2
                ;;
        esac
    fi

    return 2
}
