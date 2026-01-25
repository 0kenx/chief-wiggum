#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# security-fix.sh - Hook extensions for security-fix markdown agent
#
# This file provides hooks for the security-fix.md agent. The prompts and
# execution logic are defined in security-fix.md; this file only provides:
#   - agent_on_ready: Pre-run hook to locate report and initialize status file
#   - Helper functions for status file initialization
#
# The agent_run function is NOT defined here - it comes from agent-md.sh
# via the markdown definition.
# =============================================================================

# Source base library for helper functions
source "$WIGGUM_HOME/lib/core/agent-base.sh"

# Store located report path for reference
_SECURITY_REPORT_FILE=""

# Pre-run hook: locate upstream security-audit report and initialize status file
#
# Args:
#   worker_dir - Worker directory path
agent_on_ready() {
    local worker_dir="$1"

    # Try to find upstream report
    # Check step-config.json for optional "report_from" key (should be a step ID)
    # If not specified, scan all reports looking for one with security findings
    local step_config report_from_step
    step_config=$(agent_read_step_config "$worker_dir")
    report_from_step=$(echo "$step_config" | jq -r '.report_from // ""')

    if [ -n "$report_from_step" ]; then
        # Use the specified step ID to find the report
        _SECURITY_REPORT_FILE=$(agent_find_latest_report "$worker_dir" "$report_from_step")
    else
        # No specific step configured - find any report with security findings
        _SECURITY_REPORT_FILE=$(_find_security_audit_report "$worker_dir")
    fi

    # If no report found, nothing to fix
    if [ -z "$_SECURITY_REPORT_FILE" ] || [ ! -f "$_SECURITY_REPORT_FILE" ]; then
        log "No security-audit report found - agent will skip"
        return 0
    fi

    # Check if there are any findings to fix
    if ! grep -qE '^### (CRITICAL|HIGH|MEDIUM)' "$_SECURITY_REPORT_FILE" 2>/dev/null; then
        log "No CRITICAL/HIGH/MEDIUM findings in security report - nothing to fix"
        return 0
    fi

    # Initialize status tracking file
    local status_file="$worker_dir/reports/fix-status.md"
    _init_fix_status "$_SECURITY_REPORT_FILE" "$status_file"

    # Create stable symlink so prompts can reference a known report path
    ln -sf "$(basename "$_SECURITY_REPORT_FILE")" "$worker_dir/reports/security-report.md"

    return 0
}

# Find a security audit report file
# Scans all reports in reverse chronological order (most recent first)
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: path to report file with security findings, or empty string
_find_security_audit_report() {
    local worker_dir="$1"
    local reports_dir="$worker_dir/reports"

    [ -d "$reports_dir" ] || return 0

    # Sort by modification time (newest first) and check each for security findings
    while IFS= read -r report_file; do
        [ -f "$report_file" ] || continue
        # Check if this looks like a security audit report (has severity sections)
        if grep -qE '^### (CRITICAL|HIGH|MEDIUM|LOW|INFO)' "$report_file" 2>/dev/null; then
            echo "$report_file"
            return 0
        fi
    done < <(ls -t "$reports_dir"/*-report.md 2>/dev/null)

    return 0
}

# Initialize fix status tracking file from security report
#
# Args:
#   report_file - Path to security audit report
#   status_file - Path to create status file
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
#
# Args:
#   report_file - Path to security audit report
#   severity    - Severity level to extract (CRITICAL, HIGH, MEDIUM, etc.)
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
