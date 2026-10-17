# Extract (result, sorted axioms) pairs from Lean's `#print axioms` output in a Lake or `lean` log.
# Usage: python3 -I print-axioms-extract.py LOG | sort -u
import re, sys
t = open(sys.argv[1]).read()
t = re.sub(r"\n(?:info: )?\S+:\d+:\d+: ", "\n", t)   # drop continuation prefixes, if any
for m in re.finditer(r"(\S+) depends on axioms: \[(.*?)\]", t, re.S):
    print(m.group(1), " ".join(sorted(x.strip() for x in m.group(2).split(","))))
