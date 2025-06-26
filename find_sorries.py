#!/usr/bin/env python3
import re

def find_theorems_with_sorry(filename):
    with open(filename, 'r') as f:
        content = f.read()
    
    # Find all theorem definitions
    theorem_pattern = r'^(theorem|lemma)\s+(\w+).*?(?=^(?:theorem|lemma|def|end|example|\Z))'
    theorems = re.findall(theorem_pattern, content, re.MULTILINE | re.DOTALL)
    
    # Check each theorem for sorry
    results = []
    for match in re.finditer(theorem_pattern, content, re.MULTILINE | re.DOTALL):
        theorem_type = match.group(1)
        theorem_name = match.group(2)
        theorem_body = match.group(0)
        if 'sorry' in theorem_body:
            start_line = content[:match.start()].count('\n') + 1
            results.append((theorem_name, start_line))
    
    return results

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1:
        filename = sys.argv[1]
        results = find_theorems_with_sorry(filename)
        for name, line in results:
            print(f"{name} at line {line}")