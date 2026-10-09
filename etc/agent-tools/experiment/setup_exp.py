#!/usr/bin/env python3
"""Build the experiment template and patch the snapshot.

exp/template/  : what an agent sees (copied per run)
exp/answers/   : the original challenge proofs (for grading only)
exp/snap/      : hard-linked compiled libraries (read-only for agents)
"""
import os, re, shutil, subprocess, glob

T = '/home/ubuntu/.claude/jobs/f5d25fd8/tmp'
SRC = T + '/btree-src'
E = T + '/exp'
TPL = E + '/template'
SNAP = E + '/snap'
BT = '/home/ubuntu/etcd-grove/.claude/worktrees/btree/.lake'
CH = ['items__insertAt', 'items__find', 'node__split']
STRIP = {
    'ListLemmas.lean': ['insertAt_list', 'shiftRight_list'],
    'Lemmas/Low.lean': ['findPred', 'findPred_eq', 'sorted_lt_getElem', 'find_found', 'find_notfound'],
    'Lemmas/Struct.lean': ['ownNodes_take_drop'],
}

def lean_path():
    return ':'.join(SNAP + '/' + d for d in ['perennial', 'iris', 'qq', 'batteries', 'btree'])

def strip_decls(text, names):
    """Remove each top-level declaration `names` (with its docstring/attributes)."""
    lines = text.split('\n')
    starts = []
    for i, l in enumerate(lines):
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:theorem|lemma|def|abbrev)\s+([\w.\']+)', l)
        if m and m.group(1).split('.')[-1] in names:
            starts.append(i)
    for i in reversed(starts):
        # the end: the next line that starts a new top-level item (non-indented, non-empty)
        j = i + 1
        while j < len(lines) and not (lines[j] and not lines[j][0].isspace() and not lines[j].startswith('--')):
            j += 1
        # docstring / attribute / omit lines just before
        k = i
        while k > 0 and lines[k - 1].strip() and (lines[k - 1].startswith(('@[', 'omit', 'set_option')) or lines[k - 1].rstrip().endswith('-/') or k - 1 in range(0)):
            if lines[k - 1].rstrip().endswith('-/'):
                k -= 1
                while not lines[k].lstrip().startswith('/-'):
                    k -= 1
            else:
                k -= 1
        del lines[k:j]
    return '\n'.join(lines)

def stub(text):
    lines = text.split('\n')
    t = next(i for i, l in enumerate(lines) if l.startswith('theorem') and '.wp_proof' in l)
    e = t
    while not lines[e].rstrip().endswith(':= by'):
        e += 1
    end = next(i for i in range(len(lines) - 1, -1, -1) if lines[i].startswith('end proof'))
    return '\n'.join(lines[:e + 1] + ['  sorry', ''] + lines[end:])

shutil.rmtree(TPL, ignore_errors=True)
os.makedirs(TPL + '/EtcdGrove')
shutil.copytree(SRC + '/EtcdGrove/Btree', TPL + '/EtcdGrove/Btree')
os.remove(TPL + '/EtcdGrove/Btree/COST.md')
for f in ['Link.lean', 'Results.lean']:
    os.remove(TPL + '/EtcdGrove/Btree/' + f)
shutil.copytree(SRC + '/GoogleBtree', TPL + '/GoogleBtree')
shutil.copy(SRC + '/lean-toolchain', TPL)
os.makedirs(TPL + '/go')
shutil.copy(BT + '/goose/btree/btree_generic.go', TPL + '/go/')
# Perennial sources and docs (no build outputs, no git)
shutil.copytree(BT + '/perennial-next', TPL + '/perennial',
                ignore=shutil.ignore_patterns('.lake', '.git', '*.olean', 'go', 'testdata', 'new', 'external'))

os.makedirs(E + '/answers', exist_ok=True)
for c in CH:
    p = TPL + f'/EtcdGrove/Btree/Proof/{c}.lean'
    s = open(p).read()
    open(E + f'/answers/{c}.lean', 'w').write(s)
    open(p, 'w').write(stub(s))
for f, names in STRIP.items():
    p = TPL + '/EtcdGrove/Btree/' + f
    s = strip_decls(open(p).read(), names)
    open(p, 'w').write(s)
    left = [n for n in names if re.search(r'(?<![\w.])' + re.escape(n) + r'(?![\w\'])', s)]
    print(f, 'stripped', names, 'left', left)

# snapshot: drop the challenge modules and everything built from them
B = SNAP + '/btree/EtcdGrove'
for c in CH:
    for p in glob.glob(B + f'/Btree/Proof/{c}.*'):
        os.remove(p)
for p in glob.glob(B + '/Btree/Link.*') + glob.glob(B + '/Btree/Results.*') + glob.glob(SNAP + '/btree/EtcdGrove.*'):
    os.remove(p)
# recompile the stripped lemma modules (new files replace the hard links)
env = dict(os.environ, LEAN_PATH=lean_path(), PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
for f in ['ListLemmas.lean', 'Lemmas/Low.lean', 'Lemmas/Struct.lean']:
    mod = 'EtcdGrove/Btree/' + f[:-5]
    out = B + '/Btree/' + f[:-5]
    tmp_o, tmp_i = out + '.olean.new', out + '.ilean.new'
    r = subprocess.run(['lean', TPL + '/EtcdGrove/Btree/' + f, '-o', tmp_o, '-i', tmp_i],
                       env=env, cwd=TPL, capture_output=True, text=True)
    errs = [l for l in r.stdout.split('\n') if 'error' in l]
    print(f, 'exit', r.returncode, errs[:5])
    if r.returncode == 0:
        os.replace(tmp_o, out + '.olean')
        os.replace(tmp_i, out + '.ilean')
print('template', TPL)
