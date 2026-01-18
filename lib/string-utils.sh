#!/usr/bin/env bash
# String utility functions

# Escape special regex characters for use in sed patterns
# Usage: escape_regex_chars "string-with.special[chars]"
# Returns: string\-with\.special\[chars\]
# Note: This function is designed to work with sed using | as a delimiter
# We escape: . * [ ] \ ^ $ but NOT / since we use | as sed delimiter
escape_regex_chars() {
    local string="$1"
    # Escape all special regex characters that have meaning in sed patterns
    # Note: backslash must be escaped first, then other characters
    # We don't escape / because we use | as sed delimiter, not /
    printf '%s' "$string" | sed 's/\\/\\\\/g; s/\./\\./g; s/\*/\\*/g; s/\[/\\[/g; s/\]/\\]/g; s/\^/\\^/g; s/\$/\\$/g'
}
