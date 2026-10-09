#!/usr/bin/env python3
"""Tier 2 of the experiment: node.get and node.insert as challenges.

template2/, treatment-template2/: copies of the tier-1 templates with the two proofs stubbed and
the lemmas only they use removed; the snapshot's compiled lemma modules are rebuilt and the two
proofs' oleans deleted.
"""
import os, re, shutil, subprocess, glob

T = '/home/ubuntu/.claude/jobs/f5d25fd8/tmp'
E = T + '/exp'
SNAP = E + '/snap'
CH = ['node__get', 'node__insert']
STRIP = {
    'Lemmas/Insert.lean': ['countLt_lo', 'countLt_hi', 'items_sublist', 'elemsAux_splitChild', 'descend_child',
                           'found_item', 'leaf_insert', 'getElem?_insertAt', 'getElem?_split_left',
                           'getElem?_split_right', 'split_bounds_left', 'split_bounds_right', 'shape_set_items',
                           'shape_set_child', 'shape_splitChild', 'allItems_mem'],
    'Lemmas/Read.lean': ['lookup_of_mem', 'lookup_node_not_found'],
}
DECL = re.compile(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:theorem|lemma|def|abbrev)\s+([\w.\'?]+)')

def strip_decls(text, names):
    lines = text.split('\n')
    starts = [i for i, l in enumerate(lines)
              if (m := DECL.match(l)) and m.group(1).split('.')[-1] in names]
    for i in reversed(starts):
        j = i + 1
        while j < len(lines) and not (lines[j] and not lines[j][0].isspace() and not lines[j].startswith('--')):
            j += 1
        k = i
        while k > 0 and lines[k - 1].strip() and (lines[k - 1].startswith(('@[', 'omit', 'set_option'))
                                                  or lines[k - 1].rstrip().endswith('-/')):
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

orig = T + '/btree-src/EtcdGrove/Btree'
for src, dst in [('template', 'template2'), ('treatment-template', 'treatment-template2')]:
    d = f'{E}/{dst}'
    shutil.rmtree(d, ignore_errors=True)
    shutil.copytree(f'{E}/{src}', d, ignore=shutil.ignore_patterns('.ide.sock', '.tool-log', '.ide.err'))
    for c in CH:
        s = open(f'{orig}/Proof/{c}.lean').read()
        open(f'{E}/answers/{c}.lean', 'w').write(s)
        open(f'{d}/EtcdGrove/Btree/Proof/{c}.lean', 'w').write(stub(s))
    for f, names in STRIP.items():
        p = f'{d}/EtcdGrove/Btree/{f}'
        s = strip_decls(open(p).read(), names)
        open(p, 'w').write(s)
        left = [n for n in names if re.search(r'(?<![\w.])' + re.escape(n) + r'(?![\w\'?])', s)]
        print(dst, f, 'left:', left)

# snapshot: drop the two proofs' oleans; rebuild the stripped lemma modules
B = SNAP + '/btree/EtcdGrove/Btree'
for c in CH:
    for p in glob.glob(f'{B}/Proof/{c}.*'):
        os.remove(p)
env = dict(os.environ, LEAN_PATH=':'.join(f'{SNAP}/{x}' for x in ['perennial', 'iris', 'qq', 'batteries', 'btree']),
           PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
for f in STRIP:
    out = f'{B}/{f[:-5]}'
    r = subprocess.run(['lean', f'EtcdGrove/Btree/{f}', '-o', out + '.olean.new', '-i', out + '.ilean.new'],
                       env=env, cwd=f'{E}/template2', capture_output=True, text=True)
    print(f, 'exit', r.returncode, [l for l in r.stdout.split('\n') if 'error' in l][:5])
    if r.returncode == 0:
        os.replace(out + '.olean.new', out + '.olean')
        os.replace(out + '.ilean.new', out + '.ilean')
# the treatment's lemma index, for the new sources
r = subprocess.run(['python3', '-I', 'etc/lemma-index.py'], cwd=f'{E}/treatment-template2', capture_output=True, text=True)
print('LEMMAS.md', r.returncode, r.stdout[-300:], r.stderr[-300:])
