#!/usr/bin/env python3
"""premcheck: check a dsverify challenge's library premises, the agent's class `KitLibs`
(notes/dsv-premcheck.md; the rules: etc/PremCheck.lean's header).

Usage:
  etc/premcheck.py CONF [--no-build]   check the class, its file, the statement's premise and the
                                       non-vacuity instance; exit 1 if refused
  etc/premcheck.py --selftest [--no-build]
                                       the positive and negative tests (etc/premcheck-test/)
  etc/premcheck.py --variant SPEC OUT --kitlibs-module MOD
                                       write the KitLibs variant of a kit's statement file SPEC
                                       (`Dsverify/Spec/<pkg>/TopLevelRobustness.lean`) to OUT: its
                                       premises replaced by `KitLibs`, `kitLibs.premise` beside it
                                       (what kitgen's export writes; tested on paxos and rabia)

CONF (written by `kitgen --export-challenge` as `etc/dsv/<kit>-premcheck.conf`), `key=value` lines:
  statement_module=  the statement's module (built; imports the KitLibs module)
  spec=              the statement, `Perennial.<pkg>.<thm>.spec`
  premise=           `Perennial.<pkg>.kitLibs.premise` (the statement's KitLibs premise)
  kitlibs=           the class, `Perennial.<pkg>.KitLibs`
  kitlibs_module=    its module; kitlibs_file= its file (the text rules)
  instance=          the non-vacuity theorem (`theorem ... : kitLibs.premise`)
  instance_module=   its module (built; the only place an axiom may be declared)
  system=            a system package's Lean namespace (`rabia`, `github_com.xiang90.paxos`): one line each
  driver=            the driver's packages (denied like the system's)
  model=             the model packages (no premise may be about their functions: `net`)
  fixed=             optional: a file listing the challenge's exported modules, one per line; then
                     KitLibs.lean may import only those, and the instance's axioms outside its
                     module must be declared in them

Builds go through `lake build`; set PREMCHECK_LAKE to another command (e.g. a build-slot wrapper).
"""
import argparse
import os
import re
import shlex
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPT = 'etc/PremCheck.lean'
TEST = os.path.join(ROOT, 'etc', 'premcheck-test')


def lake(*args):
    return shlex.split(os.environ.get('PREMCHECK_LAKE', 'lake')) + list(args)


def read_conf(path):
    conf = {}
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#') or '=' not in line:
            continue
        k, v = line.split('=', 1)
        conf.setdefault(k.strip(), []).append(v.strip())
    return conf


def build(mods):
    print(f'premcheck: lake build {" ".join(mods)}', flush=True)
    r = subprocess.run(lake('build', *mods), cwd=ROOT)
    if r.returncode:
        sys.exit(f'premcheck: REFUSED: the build failed (the class, the statement and the instance must build)')


def run_lean(args):
    cmd = ['lake', 'env', 'lean', '--run', SCRIPT] + args
    r = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE, text=True)
    sys.stdout.write(r.stdout)
    return r.returncode, r.stdout


def check(conf_path, do_build=True):
    conf = read_conf(conf_path)
    need = ['statement_module', 'kitlibs_module', 'instance_module', 'kitlibs', 'spec', 'premise',
            'instance', 'kitlibs_file']
    missing = [k for k in need if k not in conf]
    if missing:
        sys.exit(f'premcheck: {conf_path} lacks {", ".join(missing)}')
    if not conf.get('system'):
        sys.exit(f'premcheck: {conf_path} names no system= package')
    mods = [conf['statement_module'][0], conf['kitlibs_module'][0], conf['instance_module'][0]]
    if do_build:
        build(mods)
    rc, _ = run_lean([f'--conf={conf_path}'] + mods)
    return rc


# ---------------------------------------------------------------------------------------------
# The selftests

def selftest(do_build=True):
    conf = os.path.join(TEST, 'selftest.conf')
    mods = [m.strip() for m in open(os.path.join(TEST, 'selftest.modules')) if m.strip()
            and not m.startswith('#')]
    if do_build:
        build(mods)
    fails = 0
    rc, out = run_lean([f'--conf={conf}', f'--selftest={os.path.join(TEST, "fields.lean")}'] + mods)
    if rc or 'FAIL' in out:
        fails += 1
    for f in sorted(os.listdir(TEST)):
        if not f.startswith('file-'):
            continue
        want_ok = f.startswith('file-ok')
        rc, out = run_lean([f'--conf={conf}', f'--file={os.path.join(TEST, f)}'] + mods)
        ok = (rc == 0) == want_ok
        print(f'premcheck: selftest {"PASS" if ok else "FAIL"} {f} '
              f'({"accept" if want_ok else "refuse"}; exit {rc})')
        fails += 0 if ok else 1
    print(f'premcheck: selftest: {"all passed" if not fails else f"{fails} FAILED"}')
    return 1 if fails else 0


# ---------------------------------------------------------------------------------------------
# The statement's KitLibs variant (the text kitgen's export writes; kitgen builds it from KITGEN)

HEAP_AT = '''/-- A machine's heap over `remoteGF` at the deployment's Go local context `lctx` (the heaps the
proof makes, one per machine): the global ghost state `G` and the local `L`, its local context
`lctx`. The premise holds of every such heap. -/
abbrev heapAt [lctx : GoLocalContext] (G : GooseGlobalGS HasLC.hasLC remoteGF)
    (L : GooseLocalGS remoteGF) : HeapGS HasLC.hasLC remoteGF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩
'''

KEEP_IMPORTS = ('TopLevelDefs', 'Net.Statement.DistDeploy', 'Robustness.Statement',
                'examples.lib.remote.counter.Shared')


def variant(spec_path, out_path, kitlibs_module):
    t = open(spec_path).read()
    pkg = re.search(r'^namespace (\S+)\n\n(?:open|attribute|/--|abbrev|def)', t, re.M)
    pkg = re.findall(r'^namespace (\S+)$', t, re.M)
    pkg = [p for p in pkg if p != 'Perennial'][0]
    thm = re.search(r'^def (\S+)\.spec : Prop :=$', t, re.M).group(1)
    body = t[t.index(f'def {thm}.spec : Prop :=\n') + len(f'def {thm}.spec : Prop :=\n'):]
    lines = body.split('\n')
    binders, i = [], 0
    while True:
        line = lines[i]
        binders.append(line)
        i += 1
        if '[go.BasicIntoValInj]' in line:
            break
    rest = [line for line in lines[i:] if line.strip()]
    deploy = next(line for line in rest if 'DistDeploy ' in line)
    robust = next(line for line in rest if 'Robustness.Robust ' in line)
    # the binder block's last line, without its trailer (`,` or the `(σ ...)` binders)
    last = binders[-1]
    last = last[:last.index('[go.BasicIntoValInj]') + len('[go.BasicIntoValInj]')]
    binders = binders[:-1] + [last]
    imports = [l for l in t.split('\n') if l.startswith('public import ')
               and any(k in l for k in KEEP_IMPORTS)]
    if not any('counter.Shared' in l for l in imports):
        imports.append('public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared')
    imports.append(f'public import {kitlibs_module}')
    doc = t[t.index('/-'):t.index('-/') + 2]
    head = doc.split('\n\n')[0].rstrip()
    if head.endswith('-/'):
        head = head[:-2].rstrip()
    o = [f'-- written by etc/premcheck.py --variant from {os.path.relpath(spec_path, ROOT)}\n',
         head + '\n\n'
         '**The challenge\'s premise**: `KitLibs` (the agent\'s class, `' + kitlibs_module + '`), at every\n'
         'machine\'s heap: what the system\'s libraries do, as `etc/premcheck.py` admits it (each field a\n'
         'Hoare triple about a library function or method, a library package\'s `InitHyp`, or library\n'
         'data; never the system\'s code, the kit\'s protocol or this conclusion), with a non-vacuity\n'
         'instance of `kitLibs.premise`. The landed kit\'s own premises are one solution.\n-/\n',
         'module\n\n']
    o += [l + '\n' for l in imports]
    o.append('\n@[expose] public section\n\nnoncomputable section\n\n'
             'set_option linter.iris.style.nameCheck false\n\nnamespace Perennial\n\n'
             'open Iris Iris.BI Net\n\n')
    o.append(f'namespace {pkg}\n\n')
    o.append('open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)\n\n')
    o.append('attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet\n\n')
    o.append(HEAP_AT + '\n')
    o.append('/-- The libraries\' premise: `KitLibs` at every machine\'s heap (the non-vacuity instance\'s type). -/\n')
    o.append('def kitLibs.premise : Prop :=\n')
    o += [b + '\n' for b in binders[:-1]]
    o.append(binders[-1] + ',\n')
    o.append('    ∀ G L, letI := heapAt G L; KitLibs remoteGF\n\n')
    o.append('/-- See the file header. -/\n')
    o.append(f'def {thm}.spec : Prop :=\n')
    o += [b + '\n' for b in binders[:-1]]
    o.append(binders[-1] + ',\n')
    o.append('    (∀ G L, letI := heapAt G L; KitLibs remoteGF) →\n')
    o.append('    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),\n')
    o.append(deploy.rstrip() + '\n')
    o.append(robust.rstrip() + '\n\n')
    o.append(f'end {pkg}\nend Perennial\n')
    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    open(out_path, 'w').write(''.join(o))
    print(f'premcheck: wrote {out_path} ({pkg}.{thm}.spec over KitLibs)')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('conf', nargs='?')
    ap.add_argument('--no-build', action='store_true')
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--variant', nargs=2, metavar=('SPEC', 'OUT'))
    ap.add_argument('--kitlibs-module')
    a = ap.parse_args()
    if a.variant:
        if not a.kitlibs_module:
            sys.exit('premcheck: --variant needs --kitlibs-module')
        variant(a.variant[0], a.variant[1], a.kitlibs_module)
        return 0
    if a.selftest:
        return selftest(not a.no_build)
    if not a.conf:
        ap.error('CONF or --selftest')
    return check(a.conf, not a.no_build)


if __name__ == '__main__':
    sys.exit(main())
