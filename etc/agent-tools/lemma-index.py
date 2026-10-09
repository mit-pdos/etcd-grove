#!/usr/bin/env python3
"""Generate LEMMAS.md: a searchable index of the btree development's lemmas.

  python3 -I etc/lemma-index.py [-o LEMMAS.md]

Every `theorem` of EtcdGrove/Btree/{ListLemmas,NodeLemmas,Model,Tree,Defs,Fractional}.lean,
EtcdGrove/Btree/Lemmas/*.lean, tools-src/BtreeLib/ListAuto.lean and Perennial's list library
(perennial/Perennial/Std/List*.lean) with its full statement, grouped by topic (keyword
rules below, first match wins), each tagged `pure` or `iris` (statement mentions an Iris
proposition), with its file:line and the `/-! ... -/` section it is in. Lemmas stated
more than once (same name or same statement) are listed under "Duplicates".
Names are shown relative to `Perennial.EtcdGrove.Btree` (btree files) or `Perennial`.
Grep it: `grep -n 'countLt' LEMMAS.md`.
"""
import os, re, sys, collections

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BT = 'EtcdGrove/Btree'
FILES = [f'{BT}/{f}' for f in ['Tree.lean', 'Model.lean', 'Defs.lean', 'Fractional.lean',
                               'ListLemmas.lean', 'NodeLemmas.lean']]
FILES += sorted(f'{BT}/Lemmas/{f}' for f in os.listdir(os.path.join(HERE, BT, 'Lemmas'))
                if f.endswith('.lean'))
FILES += ['tools-src/BtreeLib/ListAuto.lean']
FILES += sorted(f'perennial/Perennial/Std/{f}' for f in os.listdir(os.path.join(HERE, 'perennial/Perennial/Std'))
                if f.startswith('List') and f.endswith('.lean'))

DECL = re.compile(r'^\s*(?:@\[([^\]]*)\]\s*)?(?:private\s+|protected\s+)*(theorem|lemma)\s+(\S+)')
IRIS = ('⊢', 'iprop', 'IProp', '∗', '-∗', '∗-∗', 'PROP', 'WP ', '{{', '|==>')

# topic: list of regexes on "name statement"; first match wins
TOPICS = [
    ('Ownership, points-tos and node resources (Iris)', None),  # decided by the iris tag
    ('Sortedness (`Sorted`, `Pairwise`, order facts)', r'[Ss]orted|Pairwise|StrictOrder|irrefl|asymm|_lt_|lt_of|not_lt|gt_of'),
    ('Lookup and membership (`lookup`, `find?`)', r'lookup|find\?'),
    ('Insertion / deletion model (`insert`, `delete`, `removeOp`, `remIdx`)', r'insert|delete|removeOp|remIdx|InMid|RemPost|GrowMid|rem_|grow|steal|merge'),
    ('Iteration ranges (`ascRange`, `descRange`, `ascIn`, starts)', r'asc|desc|Range|iter'),
    ('`countLt` (search position)', r'countLt'),
    ('Tree shape (`Shape`, `RootBounds`, heights)', r'[Ss]hape|RootBounds|shapeOk'),
    ('In-order contents (`elems`, `elemsAux`, `pre`/`post`, child pieces)', r'elems|items_sublist|chElems|preElems|sufElems|itemsFirst|restAux|\bpre\b|\bpost\b|split_|pre_|post_'),
    ('Subslices (`subslice`)', r'subslice'),
    ('take / drop / set / insert-at / splice', r'take|drop|\.set|set_|splice|insertAt|_mid|replicate'),
    ('Lookups by index (`l[i]?`, `!!`) and lengths', r'getElem|\[[^\]]*\]\?|!!|length|lookup_lt|len'),
    ('Other list facts', r'List|list|\+\+|::'),
    ('Other', r'.'),
]


def strip_comment(line):
    i = line.find('--')
    return line if i < 0 else line[:i]


def statement(lines, i, m):
    depth, out, j, first = 0, [], i, True
    while j < len(lines) and j < i + 40:
        l = strip_comment(lines[j])
        if not first and depth == 0 and l.lstrip().startswith('|'):
            break
        seg = l[m.end():] if first else l
        first = False
        stop = None
        for k, c in enumerate(seg):
            if c in '([{⟨':
                depth += 1
            elif c in ')]}⟩':
                depth -= 1
            elif depth == 0 and seg.startswith(':=', k):
                stop = k
                break
        if stop is not None:
            out.append(seg[:stop])
            break
        out.append(seg)
        j += 1
    return re.sub(r'\s+', ' ', ' '.join(out)).strip()


def scan(path):
    lines = open(os.path.join(HERE, path)).read().split('\n')
    section = ''
    res = []
    ns = []
    for i, l in enumerate(lines):
        nm = re.match(r'^namespace\s+(\S+)', l)
        if nm:
            ns.append(nm.group(1))
        em = re.match(r'^end\s+(\S+)', l)
        if em and ns and ns[-1] == em.group(1):
            ns.pop()
        sm = re.match(r'^/-!\s*#*\s*(.*?)\s*(-/)?$', l)
        if sm and sm.group(1):
            section = sm.group(1).rstrip('-/ ').strip()
        m = DECL.match(l)
        if not m:
            continue
        attrs, _, name = m.groups()
        if name.startswith('_root_.'):
            name = name[len('_root_.'):]
        else:
            name = '.'.join(ns + [name])
        for pre in ('Perennial.EtcdGrove.Btree.', 'Perennial.'):
            if name.startswith(pre):
                name = name[len(pre):]
                break
        st = statement(lines, i, m)
        doc = ''
        if i > 0 and lines[i - 1].rstrip().endswith('-/'):
            k = i - 1
            while k >= 0 and '/--' not in lines[k]:
                k -= 1
            if k >= 0:
                doc = re.sub(r'\s+', ' ', ' '.join(lines[k:i]).replace('/--', '').replace('-/', '')).strip()
        res.append(dict(name=name, stmt=st, file=path, line=i + 1, section=section, attrs=attrs or '',
                        doc=doc, iris=any(t in st for t in IRIS)))
    return res


def topic(e):
    if e['iris']:
        return TOPICS[0][0]
    hay = e['name'] + ' ' + e['stmt']
    for t, rx in TOPICS[1:]:
        if re.search(rx, hay):
            return t
    return 'Other'


def main():
    out = 'LEMMAS.md'
    if '-o' in sys.argv:
        out = sys.argv[sys.argv.index('-o') + 1]
    entries = [e for f in FILES if os.path.exists(os.path.join(HERE, f)) for e in scan(f)]
    by_topic = collections.OrderedDict((t, []) for t, _ in TOPICS)
    for e in entries:
        by_topic[topic(e)].append(e)
    names = collections.defaultdict(list)
    stmts = collections.defaultdict(list)
    for e in entries:
        names[e['name'].split('.')[-1]].append(e)
        stmts[re.sub(r'\s', '', e['stmt'])].append(e)
    w = []
    w.append('# Lemma index (generated by `etc/lemma-index.py`; do not edit)\n')
    w.append(f'{len(entries)} lemmas from {len(FILES)} files: the btree development '
             '(`EtcdGrove/Btree/`), the `list_seg` library (`tools-src/BtreeLib/ListAuto.lean`) and '
             "Perennial's list library (`perennial/Perennial/Std/List*.lean`). "
             'Before proving a pure list fact, try `list_seg`; before writing a lemma, grep '
             'here (by name fragment or by a function in the statement: `countLt`, `elemsAux`, '
             '`take`, ...). Tags: `pure`/`iris`, `simp` if it is a simp lemma. Names are '
             'relative to `Perennial.EtcdGrove.Btree` (btree files) or `Perennial`: '
             '`InsertLemmas.foo` needs `open InsertLemmas` (or the full name).\n')
    w.append('## Topics\n')
    for t, es in by_topic.items():
        if es:
            w.append(f'- [{t}](#{re.sub(r"[^a-z0-9 -]", "", t.lower()).replace(" ", "-")}) ({len(es)})')
    w.append('')
    for t, es in by_topic.items():
        if not es:
            continue
        w.append(f'## {t}\n')
        for e in sorted(es, key=lambda e: (e['file'], e['line'])):
            tags = ['iris' if e['iris'] else 'pure'] + (['simp'] if 'simp' in e['attrs'] else [])
            sec = f' — {e["section"]}' if e['section'] else ''
            w.append(f'- **`{e["name"]}`** `{e["file"]}:{e["line"]}` [{", ".join(tags)}]{sec}  ')
            w.append(f'  `{e["stmt"]}`' + (f'  \n  {e["doc"]}' if e['doc'] else ''))
        w.append('')
    w.append('## Duplicates\n')
    w.append('Same (unqualified) name or same statement in more than one place: prefer one, '
             'they are interchangeable.\n')
    seen = set()
    for groups in (names, stmts):
        for k, es in sorted(groups.items()):
            locs = sorted({f'`{e["file"]}:{e["line"]}` {e["name"]}' for e in es})
            if len(locs) > 1 and tuple(locs) not in seen:
                seen.add(tuple(locs))
                w.append(f'- `{es[0]["name"]}`: ' + '; '.join(locs))
    open(os.path.join(HERE, out), 'w').write('\n'.join(w) + '\n')
    print(f'{out}: {len(entries)} lemmas, {sum(1 for e in entries if not e["iris"])} pure')


if __name__ == '__main__':
    main()
