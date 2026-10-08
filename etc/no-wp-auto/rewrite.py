#!/usr/bin/env python3
"""Splice the traced manual sequences (NoWpAutoTrace) into the proof sources.

usage: rewrite.py TRACE_DIR WORKTREE [--dry]
Prints statistics; writes TRACE_DIR/../rewrite-report.json with the per-site outcome.
"""
import json, os, re, sys, collections

trace_dir, root = sys.argv[1], sys.argv[2]
dry = '--dry' in sys.argv

KINDS = [('wp_auto', r'wp_auto\b'), ('wp_apply', r'wp_apply\b'), ('wp_if_destruct', r'wp_if_destruct\b'),
         ('wp_for_post', r'wp_for_post\b'), ('wp_for', r'wp_for\b'), ('wp_join', r'wp_join\b')]

def seq_of(r):
    if r['status'] == 'ok':
        s = [x for x in r['seq'] if not x.startswith('#')]
        return s
    if r['status'] == 'noprogress':
        return []
    return None  # mismatch / multigoal

def defeq(r):
    return r['status'] == 'ok' and '#defeq' in r['seq']

def wrap(indent, seq, width=100):
    """`seq` as lines `a; b; c` at `indent`, wrapped."""
    lines, cur = [], ''
    for t in seq:
        cand = t if not cur else cur + '; ' + t
        if cur and indent + len(cand) > width:
            lines.append(' ' * indent + cur)
            cur = t
        else:
            cur = cand
    if cur:
        lines.append(' ' * indent + cur)
    return lines

def lead(s):
    return len(s) - len(s.lstrip(' '))

def block_indent(line, col):
    """Indent of the tactic block the tactic at `col` is in, or None if it is not
    the first tactic of its line (after bullets)."""
    pre = line[:col]
    if re.fullmatch(r'[ ]*((·|\.)[ ]+)*', pre):
        return col
    return None

def stmt_end(lines, i, col):
    """Last line of the tactic starting at (i, col): following lines indented
    more than `col` continue it."""
    j = i
    while j + 1 < len(lines):
        nxt = lines[j + 1]
        if nxt.strip() == '' or lead(nxt) <= col:
            break
        j += 1
    return j

def block_end(lines, i, indent):
    """Last line of the bullet block starting at line i (bullet at `indent`)."""
    j = i
    while j + 1 < len(lines):
        nxt = lines[j + 1]
        if nxt.strip() == '':
            # a blank line inside a block: continue only if the next nonblank is deeper
            k = j + 1
            while k < len(lines) and lines[k].strip() == '':
                k += 1
            if k < len(lines) and lead(lines[k]) > indent:
                j = k
                continue
            break
        if lead(nxt) <= indent:
            break
        j += 1
    return j

def has_semicolon_after(text):
    depth = 0
    for ch in text:
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif ch == ';' and depth == 0:
            return True
    return False

report = []
stats = collections.Counter()

for fn in sorted(os.listdir(trace_dir)):
    if not fn.endswith('.jsonl'):
        continue
    mod = fn[:-6]
    path = os.path.join(root, mod.replace('.', '/') + '.lean')
    if not os.path.exists(path):
        print('no file for', mod); continue
    recs = collections.OrderedDict()
    for l in open(os.path.join(trace_dir, fn)):
        r = json.loads(l)
        ln, col = map(int, r['pos'].split(':'))
        recs.setdefault((ln, col), []).append(r)
    lines = open(path).read().split('\n')
    # edits: list of (line index, op, payload); applied bottom-up
    edits = []   # (i, kind, data) kind: 'replace_line' (i, [lines]) | 'insert_before' | 'insert_after'
    def todo(i, col, msg):
        edits.append((i, 'insert_before', [' ' * lead(lines[i]) + '-- TODO(no-wp-auto): ' + msg]))
    per_line = collections.Counter(ln for (ln, _) in recs)
    for (ln, col), rs in recs.items():
        i = ln - 1
        line = lines[i]
        rest = line[col:]
        if per_line[ln] > 1:
            site = {'file': path[len(root) + 1:], 'line': ln, 'col': col, 'kind': 'several-on-line',
                    'n': len(rs), 'statuses': [r['status'] for r in rs], 'defeq': False,
                    'outcome': 'manual-line'}
            report.append(site)
            if any(seq_of(r) for r in rs):
                todo(i, col, f'col {col}: ' + ' | '.join('; '.join(seq_of(r)) if seq_of(r) is not None else '?' for r in rs))
            continue
        kind = None
        for k, rx in KINDS:
            if re.match(rx, rest):
                kind = k; break
        seqs = [seq_of(r) for r in rs]
        site = {'file': path[len(root) + 1:], 'line': ln, 'col': col, 'kind': kind or rest[:30],
                'n': len(rs), 'statuses': [r['status'] for r in rs], 'defeq': any(defeq(r) for r in rs)}
        report.append(site)
        if any(s is None for s in seqs):
            site['outcome'] = 'mismatch'
            todo(i, col, f'{site["kind"]}: no manual sequence found ({[r["status"] for r in rs]})')
            continue
        uniq = []
        for s in seqs:
            if s not in uniq:
                uniq.append(s)
        if kind is None:
            site['outcome'] = 'macro'
            if any(seqs):
                todo(i, col, f'macro `{rest.split()[0] if rest.split() else rest}` runs wp_auto: ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
            continue
        if kind == 'wp_auto':
            if len(uniq) != 1:
                site['outcome'] = 'manual-multi'
                todo(i, col, 'wp_auto (several runs): ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
                continue
            seq = uniq[0]
            pre, post = line[:col], line[col + len('wp_auto'):]
            m = re.search(r'try\s*$', pre)
            if m:
                pre = pre[:m.start()]
            elif not seq:
                site['outcome'] = 'manual-empty'
                todo(i, col, 'wp_auto made no progress (?)')
                continue
            alone_pre = re.fullmatch(r'[ ]*((·|\.)[ ]+)*', pre) is not None
            alone_post = re.fullmatch(r'\s*(--.*)?', post) is not None
            if not seq:
                # `try wp_auto` that never made progress: drop it
                if alone_pre and alone_post and pre.strip() == '':
                    edits.append((i, 'replace_line', []))
                    site['outcome'] = 'dropped'
                    continue
                newline = (pre + post.lstrip()).rstrip()
                newline = re.sub(r';\s*$', '', newline)
                newline = re.sub(r'^(\s*(?:·\s*)?);\s*', r'\1', newline)
                newline = re.sub(r'\(\s*;\s*', '(', newline)
                newline = re.sub(r';\s*;', ';', newline)
                if newline.strip() in ('', '·'):
                    site['outcome'] = 'manual-empty'
                    todo(i, col, 'try wp_auto (no progress) alone')
                    continue
                edits.append((i, 'replace_line', [newline]))
                site['outcome'] = 'dropped'
                continue
            if alone_pre and alone_post:
                ws = wrap(len(pre), seq)
                ws[0] = pre + ws[0][len(pre):]
                if post.strip():
                    ws[-1] += ' ' + post.strip()
                edits.append((i, 'replace_line', ws))
            else:
                txt = seq[0] if len(seq) == 1 else '(' + '; '.join(seq) + ')'
                edits.append((i, 'replace_line', [pre + txt + post]))
            site['outcome'] = 'replaced'
            continue
        # implicit sites
        if kind in ('wp_apply', 'wp_for_post'):
            if len(uniq) == 1 and not uniq[0]:
                site['outcome'] = 'nothing'; continue
            if len(uniq) != 1:
                site['outcome'] = 'manual-multi'
                todo(i, col, f'{kind} (several runs): ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
                continue
            seq = uniq[0]
            bi = block_indent(line, col)
            j = stmt_end(lines, i, col)
            stmt_text = '\n'.join([lines[i][col:]] + lines[i + 1:j + 1])
            if bi is None or has_semicolon_after(stmt_text.split('--')[0]):
                site['outcome'] = 'manual-inline'
                todo(i, col, f'{kind} then: ' + '; '.join(seq))
                continue
            # skip the premise bullets
            k = j
            while k + 1 < len(lines) and lines[k + 1].strip().startswith('·') and lead(lines[k + 1]) == bi:
                k = block_end(lines, k + 1, bi)
            edits.append((k, 'insert_after', wrap(bi, seq)))
            site['outcome'] = 'inserted' + ('-after-bullets' if k != j else '')
            continue
        if kind == 'wp_for':
            if len(rs) != 2 or len(uniq) > 2:
                if all(not s for s in seqs):
                    site['outcome'] = 'nothing'; continue
                site['outcome'] = 'manual-multi'
                todo(i, col, 'wp_for runs: ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
                continue
            s1, s2 = seqs
            if not s1 and not s2:
                site['outcome'] = 'nothing'; continue
            bi = block_indent(line, col)
            j = stmt_end(lines, i, col)
            if bi is None or j != i:
                site['outcome'] = 'manual-inline'
                todo(i, col, 'wp_for runs: ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
                continue
            m = re.match(r'wp_for(\s+(\w+))?\s*(--.*)?$', rest)
            if not m:
                site['outcome'] = 'manual-inline'
                todo(i, col, 'wp_for runs: ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
                continue
            if s1:
                new = [line[:col] + 'wp_for_core']
                if m.group(2):
                    new.append(' ' * bi + f'iNamed {m.group(2)}')
                new += wrap(bi, s1) + [' ' * bi + 'cleanup_bool_decide'] + wrap(bi, s2)
                edits.append((i, 'replace_line', new))
            else:
                edits.append((i, 'insert_after', wrap(bi, s2)))
            site['outcome'] = 'replaced'
            continue
        if kind == 'wp_if_destruct':
            if all(not s for s in seqs):
                site['outcome'] = 'nothing'; continue
            if len(rs) != 2:
                site['outcome'] = 'manual-multi'
                todo(i, col, 'wp_if_destruct runs: ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
                continue
            s1, s2 = seqs
            bi = block_indent(line, col)
            j = stmt_end(lines, i, col)
            if bi is None or j != i or not re.fullmatch(r'wp_if_destruct\s*(--.*)?', rest.strip()):
                site['outcome'] = 'manual-inline'
                todo(i, col, 'wp_if_destruct runs: ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
                continue
            nxt = j + 1
            while nxt < len(lines) and lines[nxt].strip() == '':
                nxt += 1
            if nxt < len(lines) and lead(lines[nxt]) == bi and lines[nxt].strip().startswith('·'):
                # case 1 is the bullet at `nxt`
                b1 = nxt
                e1 = block_end(lines, b1, bi)
                n2 = e1 + 1
                while n2 < len(lines) and lines[n2].strip() == '':
                    n2 += 1
                if s1:
                    edits.append((b1, 'bullet_prefix', (bi, s1)))
                if s2:
                    if n2 < len(lines) and lead(lines[n2]) == bi and lines[n2].strip().startswith('·'):
                        edits.append((n2, 'bullet_prefix', (bi, s2)))
                    elif n2 < len(lines) and lead(lines[n2]) == bi:
                        edits.append((e1, 'insert_after', wrap(bi, s2)))
                    else:
                        site['outcome'] = 'manual-structure'
                        todo(i, col, 'wp_if_destruct runs: ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
                        continue
                site['outcome'] = 'bullets'
            else:
                new = []
                if s2:
                    new += [' ' * bi + 'rotate_left'] + wrap(bi, s2) + [' ' * bi + 'rotate_right']
                new += wrap(bi, s1)
                edits.append((i, 'insert_after', new))
                site['outcome'] = 'rotate'
            continue
        if kind == 'wp_join':
            if all(not s for s in seqs):
                site['outcome'] = 'nothing'; continue
            site['outcome'] = 'manual-join'
            todo(i, col, 'wp_join runs (cont first, then the cases): ' + ' | '.join('; '.join(s) or '∅' for s in seqs))
            continue
    # apply edits bottom-up (stable for same line: insert_before last)
    order = {'insert_after': 0, 'bullet_prefix': 1, 'replace_line': 2, 'insert_before': -1}
    edits.sort(key=lambda e: (e[0], order[e[1]]), reverse=True)
    # several edits to the same line: replace_line and bullet_prefix conflict
    seen = collections.Counter((e[0], e[1]) for e in edits)
    for (i, op), n in seen.items():
        if n > 1 and op in ('replace_line', 'bullet_prefix'):
            print('conflict', path, i + 1, op)
    for i, op, data in edits:
        if op == 'replace_line':
            lines[i:i + 1] = data
        elif op == 'insert_after':
            lines[i + 1:i + 1] = data
        elif op == 'insert_before':
            lines[i:i] = data
        elif op == 'bullet_prefix':
            bi, seq = data
            l = lines[i]
            m = re.match(r'(\s*·\s*)(.*)$', l)
            if m is None:
                print('bullet_prefix on a non-bullet line', path, i + 1, repr(l))
                lines[i:i] = [' ' * bi + '-- TODO(no-wp-auto): branch steps: ' + '; '.join(seq)]
                continue
            body = m.group(2)
            inner = bi + 2
            ws = wrap(inner, seq)
            ws[0] = ' ' * bi + '· ' + ws[0].lstrip()
            if body.strip():
                ws.append(' ' * inner + body)
            lines[i:i + 1] = ws
    stats.update(s.get('outcome') for s in report if s['file'] == path[len(root) + 1:])
    if not dry:
        open(path, 'w').write('\n'.join(lines))

json.dump(report, open(os.path.join(os.path.dirname(trace_dir.rstrip('/')), 'rewrite-report.json'), 'w'), indent=1)
for k, v in sorted(stats.items(), key=lambda x: -x[1]):
    print(f'{v:6d} {k}')
kinds = collections.Counter((s['kind'] if s['kind'] in dict(KINDS) else 'macro/other') for s in report)
print(kinds)
print('defeq sites', sum(s['defeq'] for s in report))
