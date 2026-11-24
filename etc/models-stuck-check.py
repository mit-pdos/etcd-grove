#!/usr/bin/env python3
"""The models' not-modelled points call a stuck stub (models/README.md, "Not modelled: stuck").

Checks the Go sources (but tests) of models/ and examples/ and the generators' Python under models/
(git ls-files; old/ excluded):

  - every `MODEL: not modelled (stuck)` marker is on a line that calls a stub, or on a comment
    line whose comment block is followed by a line that calls one;
  - no `select {}` outside a stub's body (a bare empty select is not a sound stuck point: its WP,
    `chan.wp_select_blocking []`, has the precondition True and proves anything after it).

A stub is a function named `stuck`, `Stuck` or `rpcStuck` whose Go body is `select {}` and whose Lean
model is Perennial's `internal.gomodel.Stuck.impl` (the package's goose configuration lists it as
trusted); a call is `stuck()`, `Stuck()`, `rpcStuck()` or a qualified `X.Stuck()`. Exits 1 on a
violation, listing each.
"""
import re
import subprocess
import sys

STUB_CALL = re.compile(r'(?<![\w.])(?:stuck|Stuck|rpcStuck)\(\)|\b\w+\.Stuck\(\)')
STUB_DEF = re.compile(r'^func (?:stuck|Stuck|rpcStuck)\(\) \{')
MARK_ALONE = re.compile(r'^\s*// MODEL: not modelled \(stuck\)')
MARK_TRAIL = re.compile(r'\S.*// MODEL: not modelled \(stuck\)')
EMPTY_SELECT = re.compile(r'^\s*select \{\}')


def files():
    out = subprocess.run(['git', 'ls-files', 'models/*.go', 'examples/*.go', 'models/*.py'],
                         capture_output=True, text=True, check=True).stdout.split()
    return [f for f in out if not f.endswith('_test.go') and not f.startswith('old/')]


def check(path):
    bad = []
    lines = open(path, encoding='utf-8').read().split('\n')
    in_stub = False
    for i, line in enumerate(lines):
        if path.endswith('.py'):
            line = line.replace('\\t', ' ')  # a generator's Go text, its tabs escaped
        if STUB_DEF.match(line):
            in_stub = True
        elif in_stub and line.startswith('}'):
            in_stub = False
        if path.endswith('.go') and EMPTY_SELECT.match(line) and not in_stub:
            bad.append(f'{path}:{i + 1}: an empty select outside a stub (call the package\'s stuck stub)')
        if MARK_TRAIL.search(line):
            if not STUB_CALL.search(line.split('// MODEL: not modelled (stuck)')[0]):
                bad.append(f'{path}:{i + 1}: a not-modelled marker on a line that calls no stub')
        elif MARK_ALONE.match(line):
            j = i + 1
            while j < len(lines) and lines[j].lstrip().startswith('//'):
                j += 1
            if j >= len(lines) or not STUB_CALL.search(lines[j]):
                bad.append(f'{path}:{i + 1}: a not-modelled marker not followed by a stub call')
    return bad


def main():
    bad = [b for f in files() for b in check(f)]
    for b in bad:
        print(b)
    if bad:
        print(f'models-stuck-check: {len(bad)} violation(s)')
        sys.exit(1)
    print('models-stuck-check: ok')


if __name__ == '__main__':
    main()
