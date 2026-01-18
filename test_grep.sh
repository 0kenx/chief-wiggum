#!/usr/bin/env bash

temp=$(mktemp)
echo '- [x] **[TASK-012[bar]]** Test task' > "$temp"
echo "File contents: $(cat $temp)"

# Test different grep approaches
echo ""
echo "Testing grep -F (literal string search):"
if grep -F '- [x]' "$temp"; then
    echo "✓ Found with grep -F"
fi

echo ""
echo "Testing grep without -F:"
if grep '- \[x\]' "$temp"; then
    echo "✓ Found with grep (escaped)"
fi

echo ""
echo "Testing echo with grep -F:"
if echo "$(cat $temp)" | grep -F '- [x]'; then
    echo "✓ Found with echo | grep -F"
fi

rm "$temp"
