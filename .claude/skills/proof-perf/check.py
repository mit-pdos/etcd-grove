#!/usr/bin/env python3
"""Check a proof-performance branch against the rules of SKILL.md that a script can check.

Usage: .claude/skills/proof-perf/check.py [--base REV]

Compares the working tree (committed or not) with REV (default: the merge base with
`origin/lean`). Prints FAIL lines (a rule is broken: undo that change) and WARN lines
(look at each and say in the report why it is fine), and exits 1 if there is a FAIL.
It checks the text of the change only; that the results still say the same is
`fingerprint.py --diff`'s, and the axioms and `sorry`s `etc/tcb-report.py --check`'s.
"""

import argparse
import re
import subprocess
import sys

# What a performance change may touch: proofs, and the status notes.
ALLOWED = [
    r"Proof/.*\.lean",
    r"notes/STATUS\.md",
]
# Under Proof/, the files that are generated (CLAUDE.md: never edit them by hand) or
# that hold trust-boundary axioms.
GENERATED = [
    r"Proof/.*/Link\.lean",
    r"Proof/.*/Init\.lean",
    r"Proof/.*/Initialize\.lean",
]

# Added text that weakens what the kernel checks, or adds to the trust base.
FORBIDDEN = [
    (r"\bsorry\b", "`sorry`"),
    (r"\badmit\b", "`admit`"),
    (r"^\s*(@\[[^\]]*\]\s*)?(private\s+|protected\s+|noncomputable\s+)*axiom\b", "an axiom"),
    (r"\bnative_decide\b", "`native_decide`"),
    (r"\bdecide\s*\+\s*native\b|\bdecide\s*\(\s*config\s*:=\s*\{[^}]*native", "`decide +native`"),
    (r"@\[\s*implemented_by", "`implemented_by`"),
    (r"@\[\s*extern", "`extern`"),
    (r"\bunsafe\b", "`unsafe`"),
    (r"debug\.skipKernelTC", "`debug.skipKernelTC`"),
    (r"^\s*(private\s+)?opaque\b", "`opaque`"),
    (r"\bofReduceBool\b|\bofReduceNat\b", "`ofReduceBool`/`ofReduceNat`"),
    (r"\bLean\.Elab\.Command\.addDecl|\baddDecl\b", "a declaration added by meta code"),
]
# Added or removed text a reviewer should look at.
SUSPECT = [
    (r"^\s*(@\[[^\]]*\]\s*)?(private\s+|protected\s+|noncomputable\s+|partial\s+)*"
     r"(def|abbrev|structure|inductive|class|instance|opaque)\b",
     "a definition (the fingerprint says whether a result's statement reaches it)"),
    (r"\bmaxHeartbeats\b|\bmaxRecDepth\b|\bsynthInstance\.maxHeartbeats\b",
     "a resource limit"),
    (r"^\s*(elab|macro|syntax|macro_rules|elab_rules|run_cmd|run_tac|run_elab|initialize)\b",
     "meta code (a tactic or command of its own)"),
    (r"^\s*(attribute\s*\[|@\[[^\]]*\b(simp|instance|reducible|irreducible|semireducible)\b)",
     "an attribute (proof-only, unless it changes how a statement elaborates)"),
]

failures = 0


def fail(msg):
    global failures
    failures += 1
    print(f"FAIL {msg}")


def warn(msg):
    print(f"WARN {msg}")


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--base", help="the revision to compare with (default: merge base with origin/lean)")
    a = p.parse_args()
    base = a.base or git("merge-base", "HEAD", "origin/lean").strip()

    changed = [l.split("\t") for l in git("diff", "--name-status", "-M", base).splitlines()]
    untracked = git("ls-files", "--others", "--exclude-standard").splitlines()
    paths = []
    for row in changed:
        paths += row[1:]
    paths += untracked
    for path in sorted(set(paths)):
        if not any(re.fullmatch(r, path) for r in ALLOWED):
            fail(f"{path}: outside what a performance change may touch")
        elif any(re.fullmatch(r, path) for r in GENERATED):
            fail(f"{path}: a generated file (regenerate it with its script, never edit; "
                 "keep the module that a `Link.lean` imports where it is)")
    for path in untracked:
        if path.endswith(".lean"):
            warn(f"{path}: a new file (not yet committed): checked as all added lines")

    diff = git("diff", "-U0", base, "--", "*.lean")
    for path in untracked:
        if path.endswith(".lean"):
            with open(path, encoding="utf-8") as f:
                diff += f"+++ b/{path}\n" + "".join("+" + l for l in f)
    file = None
    in_comment = False
    for line in diff.splitlines():
        if line.startswith("+++ "):
            file = line[6:] if line.startswith("+++ b/") else None
            continue
        if line.startswith("--- ") or line.startswith("@@") or file is None:
            continue
        if not line[:1] in "+-":
            continue
        sign, text = line[0], line[1:]
        # Comments and docstrings may mention anything.
        code = re.sub(r"--.*$", "", text)
        if "/-" in code:
            in_comment = "-/" not in code.split("/-", 1)[1]
            code = code.split("/-", 1)[0]
        elif in_comment:
            if "-/" in code:
                in_comment = False
                code = code.split("-/", 1)[1]
            else:
                continue
        if sign == "+":
            for pat, what in FORBIDDEN:
                if re.search(pat, code):
                    fail(f"{file}: adds {what}: {text.strip()[:120]}")
        for pat, what in SUSPECT:
            if re.search(pat, code):
                verb = "adds" if sign == "+" else "removes"
                warn(f"{file}: {verb} {what}: {text.strip()[:120]}")

    shown = base[:10] if re.fullmatch(r"[0-9a-f]{40}", base) else base
    print(f"check: {len(set(paths))} paths changed against {shown}; "
          f"{failures} FAIL")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
