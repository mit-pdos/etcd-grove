#!/usr/bin/env python3
"""Grade a challenge run: the proof compiles under the baseline checker with no sorry,
the theorem statement is unchanged, and it depends on no unexpected axioms.

usage: grade.py RUN_DIR CHALLENGE      (prints one JSON line)
"""
import json, os, re, subprocess, sys

E = '/home/ubuntu/.claude/jobs/f5d25fd8/tmp/exp'
run, ch = sys.argv[1], sys.argv[2]
NAMES = {'items__insertAt': 'items.insertAt.wp_proof', 'items__find': 'items.find.wp_proof',
         'node__split': 'node.split.wp_proof', 'node__get': 'node.get.wp_proof',
         'node__insert': 'node.insert.wp_proof'}
f = f'{run}/EtcdGrove/Btree/Proof/{ch}.lean'
src = open(f).read()
tpl = 'template2' if ch in ('node__get', 'node__insert') else 'template'
stub = open(f'{E}/{tpl}/EtcdGrove/Btree/Proof/{ch}.lean').read()

def header(s):
    i = s.index('theorem ' + NAMES[ch].split('.wp_proof')[0])
    return re.sub(r'\s+', ' ', s[i:s.index(':= by', i)])

res = {'run': os.path.basename(run), 'challenge': ch}
res['statement_unchanged'] = header(src) == header(stub)
res['sorry_in_source'] = bool(re.search(r'\bsorry\b|\badmit\b', src))
tmp = f'{run}/.grade_{ch}.lean'
open(tmp, 'w').write(src + f'\n#print axioms Perennial.EtcdGrove.Btree.{NAMES[ch]}\n')
snap = E + '/snap'
# the treatment's precompiled tool modules (`import GroveTools`); unused by baseline proofs
env = dict(os.environ, LEAN_PATH=':'.join([f'{snap}/{d}' for d in ['perennial', 'iris', 'qq', 'batteries', 'btree']]
                                         + [E + '/toolsbuild']),
           PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
r = subprocess.run(['lean', tmp], cwd=run, env=env, capture_output=True, text=True, timeout=3600)
os.remove(tmp)
out = r.stdout + r.stderr
res['errors'] = len(re.findall(r': error:', out))
res['sorry_warning'] = 'declaration uses `sorry`' in out or 'sorryAx' in out
m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
axioms = sorted(a.strip() for a in m.group(1).split(',')) if m else None
res['axioms'] = axioms
# the axioms a known-good btree proof (items.truncate, node.get) depends on: the standard
# three and Perennial's axiomatized library types
std = {'propext', 'Classical.choice', 'Quot.sound'} | {'Perennial.' + x for x in (
    'fmt.pp fmt.readRune strings.Replacer strings.replacer strings.stringWriter sync.Map '
    'sync.poolChainElt internal.synctest.CurrentBubble internal.synctest.OtherBubble '
    'internal.synctest.Unbubbled').split()} | {'Perennial.' + x + s for x in (
    'fmt.pp fmt.readRune strings.Replacer strings.replacer strings.stringWriter sync.Map '
    'sync.poolChainElt').split() for s in ('.underlying', '.zero_val')}
res['extra_axioms'] = [a for a in (axioms or []) if a not in std]
res['pass'] = (r.returncode == 0 and res['errors'] == 0 and not res['sorry_warning'] and
               res['statement_unchanged'] and not res['sorry_in_source'] and axioms is not None and
               not res['extra_axioms'])
res['proof_lines'] = len(src.split('\n')) - len(stub.split('\n')) + 1
print(json.dumps(res))
