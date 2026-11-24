#!/usr/bin/env python3
# Usage: etc/dsv/compare.py RUN... (as root; RUN as for tokens.py: a name under $DSV_LAB/runs, or a
# path): the runs side by side, from their transcripts, the project's git history (all branches) and the
# run's logs. Times are active minutes from the run's first transcript line: a pause (no transcript line
# for tokens.PAUSE minutes, e.g. a usage limit) does not count.
#   cost        wall clock, responses, output and total tokens, subagents
#   questions   AskUserQuestion calls, and how many the run's hook (ask-hook.sh) answered
#   process     decisions logged; review subagents and review notes; every Spec/ file: when first
#               committed, how often changed later; the median function proof (Proof/X.lean with a
#               Spec/X.lean, first committed without `sorry`) and the specs added or changed after it; the
#               same after the freeze tag (the last tag named *froz*/*freez*: the last stage's; its
#               commit's time)
#   backtrack   from the per-minute snapshots, when the run has them (backtrack.py: spec and proof
#               rewrites, invalidated proofs, cascades, churn)
#   result      the last verify-TAG.log's verdict; the host's load (load.log)
# "spec-first phases" sums up whether a run did what the dsverify skill's spec-first workflow asks
# before proving: a review round, a freeze before the median function proof, and every spec written
# before it. A run without them did not receive the spec-first treatment, whatever its skill; report it
# separately.
import glob, json, os, re, subprocess, sys
from datetime import datetime, timezone
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tokens, backtrack

HOOK_REPLY = 'No user is available during this run'


def ts(s):
    return datetime.fromisoformat(s.replace('Z', '+00:00'))


def git(d, *a):
    return subprocess.run(['git', '-c', 'safe.directory=*', '-C', d, *a], capture_output=True, text=True).stdout


def skill_tree(line):
    # the tree of the skill the run got (meta.txt's "skill:" line, "tree X"), so runs with the same
    # skill match whichever commit named it
    t = re.search(r'tree ([0-9a-f]{40})', line)
    if t: return t.group(1)[:7]
    return 'none' if line.strip().startswith('none') else '-'


def project(run):
    """The project repo: a git repository with a lakefile under home/work (not in .lake)."""
    W = os.path.join(run, 'home/work')
    # not a worktree (.git a file), not under deps/ (checkouts of dependencies, e.g. deps/perennial,
    # which a bump seed moves to a pin detached), and not a plain clone of an upstream repo (HEAD on
    # a remote branch)
    c = [os.path.dirname(f) for f in glob.glob(W + '/*/lakefile.toml') + glob.glob(W + '/*/*/lakefile.toml')
         if '/.lake/' not in f and not f.startswith(W + '/deps/')
         and os.path.isdir(os.path.join(os.path.dirname(f), '.git'))]
    c = [d for d in c if not git(d, 'branch', '-r', '--contains', 'HEAD').strip()]
    # a challenge run (sandbox.sh new --challenge): the work tree itself is the project
    if os.path.isfile(os.path.join(run, 'goal/challenge')) and os.path.isdir(os.path.join(W, '.git')):
        return W
    return c[0] if len(c) == 1 else None


def final_ref(P):
    """The result's commit: the tag `final`, else the newest branch (the agent may work in a worktree)."""
    if git(P, 'rev-parse', '-q', '--verify', 'refs/tags/final').strip(): return 'final'
    return git(P, 'for-each-ref', '--sort=-committerdate', '--format=%(refname:short)', 'refs/heads').split('\n')[0]


def transcript_facts(run):
    asks, answered = set(), set(); review = sub = 0  # by tool-use id: a response spans several lines
    for f, who in tokens.transcripts(run):
        first = None
        for l in open(f):
            e = json.loads(l); m = e.get('message') or {}; c = m.get('content')
            if who == 'subagents' and first is None and e.get('type') == 'user':
                first = c if isinstance(c, str) else ' '.join(x.get('text', '') for x in c if isinstance(x, dict))
            if not isinstance(c, list): continue
            for x in c:
                if x.get('type') == 'tool_use' and x.get('name') == 'AskUserQuestion': asks.add(x.get('id'))
                if x.get('type') == 'tool_result' and HOOK_REPLY in json.dumps(x.get('content')): answered.add(x.get('tool_use_id'))
        if who == 'subagents':
            sub += 1
            # a reviewer's brief asks it to review (rank, critique) specs, not to prove them
            if first and re.search(r'\breview', first, re.I) and not re.search(r'\bprove\b', first[:300], re.I):
                review += 1
    return dict(asks=len(asks), answered=len(answered), subagents=sub, reviewers=review)


def git_facts(P, m):
    tags = {}
    # an annotated tag counts from when it was made (taggerdate), a lightweight one from its commit
    for line in git(P, 'for-each-ref', '--format=%(refname:short) %(taggerdate:unix) %(committerdate:unix)', 'refs/tags').split('\n'):
        if line.strip():
            name, *u = line.split(); u = [x for x in u if x]
            tags[name] = m(datetime.fromtimestamp(int(u[0]), timezone.utc))
    frz = [t for n, t in tags.items() if re.search(r'froz|freez', n, re.I)]
    freeze = max(frz) if frz else None   # the last stage's freeze (stage0-frozen is the model's, before any proof)
    specs = {}; proofs = {}
    for f in git(P, 'log', '--all', '--format=%x00%ct', '--name-only', '--diff-filter=AM').split('\0'):
        lines = [x for x in f.split('\n') if x.strip()]
        if not lines: continue
        t = m(datetime.fromtimestamp(int(lines[0]), timezone.utc))
        for p in lines[1:]:
            if p.endswith('.lean') and '.lake' not in p:
                for d, k in ((specs, '/Spec/'), (proofs, '/Proof/')):
                    if k in p: d.setdefault(p, set()).add(round(t, 2))
    first = {p: min(v) for p, v in specs.items()}
    # function proofs: each Proof/X.lean whose Spec/X.lean exists is proved at the first commit where it
    # has no `sorry` (drafts commit stubs). A few early proofs are expected (probes, leaf packages); the
    # median proof is when proving is under way.
    def proved(q):
        for line in git(P, 'log', '--all', '--reverse', '--format=%ct %H', '--', q).split('\n'):
            if line.strip():
                u, h = line.split()
                body = git(P, 'show', '%s:%s' % (h, q))
                if body and not re.search(r'\bsorry\b', body):
                    return m(datetime.fromtimestamp(int(u), timezone.utc))
        return None
    fp = sorted(t for t in (proved(q) for q in (p.replace('/Spec/', '/Proof/') for p in specs) if q in proofs)
                if t is not None)
    first_proof = fp[len(fp) // 2] if fp else None
    med = lambda v: sorted(v)[len(v) // 2] if v else None
    spec_med = med(list(first.values()))
    changes = [t for v in specs.values() for t in sorted(v)[1:]]
    main_spec = [t for p, t in first.items() if p.endswith('/Main.lean')]
    reviews = [f for f in git(P, 'ls-tree', '-r', '--name-only', final_ref(P), 'notes').split('\n')
               if re.search(r'review', f, re.I)]
    return dict(
        tags=', '.join('%s@%.0f' % (n, t) for n, t in sorted(tags.items(), key=lambda x: x[1])) or 'none',
        freeze=freeze, specs=len(specs), changes=len(changes),
        first_span='%.0f-%.0f' % (min(first.values()), max(first.values())) if first else '-',
        main_spec='%.0f' % main_spec[0] if main_spec else '-',
        after_freeze_new=sum(t > freeze for t in first.values()) if freeze is not None else None,
        after_freeze_changed=sum(t > freeze for t in changes) if freeze is not None else None,
        proofs_by_freeze=sum(t <= freeze for t in fp) if freeze is not None else None,
        review_notes=len(reviews), first_proof=first_proof, spec_med=spec_med, nproofs=len(fp),
        after_proof_new=sum(t > first_proof for t in first.values()) if first_proof is not None else None,
        after_proof_changed=sum(t > first_proof for t in changes) if first_proof is not None else None,
        last=max(m(datetime.fromtimestamp(int(x), timezone.utc)) for x in git(P, 'log', '--all', '--format=%ct').split()))


def facts(run):
    u = tokens.usage(run)
    if not u['start']: return {'run': os.path.basename(run.rstrip('/')), 'note': 'no transcript'}
    t0, t1 = ts(u['start']), ts(u['end'])
    _, active, pauses = tokens.clock(run)
    r = dict(run=os.path.basename(run.rstrip('/')))
    meta = open(os.path.join(run, 'meta.txt')).read() if os.path.exists(os.path.join(run, 'meta.txt')) else ''
    s = re.search(r'^skill: *(.*)$', meta, re.M); h = re.search(r'[0-9a-f]{7,}', s.group(1)) if s else None
    r['skill'] = h.group(0)[:7] if h else (s.group(1).strip() or 'none') if s else '-'
    if s: r['skill tree'] = skill_tree(s.group(1))
    r['active (min)'] = '%.0f' % active(t1)
    r['paused (min)'] = '%.0f' % sum((b - a).total_seconds() / 60 for a, b in pauses) if pauses else '0'
    r['responses'] = u['responses']
    r['output tokens'] = '{:,}'.format(u['all']['output_tokens'])
    r['total tokens'] = '{:,}'.format(sum(u['all'].values()))
    tot = sum(u['all'].values()) or 1
    r['in subagents'] = '%.0f%%' % (100 * sum(u['subagents'].values()) / tot)
    tf = transcript_facts(run)
    r['subagents'] = tf['subagents']; r['review subagents'] = tf['reviewers']
    r['questions (hook-answered)'] = '%d (%d)' % (tf['asks'], tf['answered'])
    P = project(run)
    dec = git(P, 'show', final_ref(P) + ':notes/decisions.md') if P else ''
    r['decisions'] = len(re.findall(r'^## ', dec, re.M)) if dec else '-'
    if P:
        g = git_facts(P, active)
        r['last commit (min)'] = '%.0f' % g['last']
        r['tags (min)'] = g['tags']
        r['review notes'] = g['review_notes']
        r['spec files'] = g['specs']; r['first committed (min)'] = g['first_span']
        r['Main spec (min)'] = g['main_spec']; r['later spec changes'] = g['changes']
        fp = g['first_proof']
        r['median spec / median proof (min)'] = '%s / %s (%d proofs)' % (
            '%.0f' % g['spec_med'] if g['spec_med'] is not None else '-',
            '%.0f' % fp if fp is not None else '-', g['nproofs'])
        r['specs added / changed after median proof'] = ('%d / %d' % (g['after_proof_new'], g['after_proof_changed'])
                                                        if fp is not None else '-')
        r['freeze (min)'] = '%.0f' % g['freeze'] if g['freeze'] is not None else 'none'
        r['proofs finished by the freeze'] = ('%d of %d' % (g['proofs_by_freeze'], g['nproofs'])
                                              if g['freeze'] is not None else '-')
        r['specs added / changed after freeze'] = ('%d / %d' % (g['after_freeze_new'], g['after_freeze_changed'])
                                                  if g['freeze'] is not None else '-')
        phases = [('review', tf['reviewers'] > 0 or g['review_notes'] > 0),
                  ('freeze before proofs', g['freeze'] is not None and fp is not None and g['freeze'] <= fp),
                  ('specs before most proofs', fp is not None and g['after_proof_new'] == 0)]
        r['spec-first phases'] = ', '.join(('' if ok else 'NO ') + n for n, ok in phases)
    if os.path.isdir(os.path.join(run, 'snapshots.git')):   # backtracking, from the work-tree snapshots
        b = backtrack.analyze(run)
        if b:
            for k, v in b[0].items():
                if k not in ('run', 'span', 'spec files'): r['snap: ' + k] = v
    logs = sorted(glob.glob(os.path.join(run, 'verify-*.log')), key=os.path.getmtime)
    if logs:
        v = [l for l in open(logs[-1]) if re.match(r'== (NOT )?verified', l)]
        r['verify'] = '%s: %s' % (os.path.basename(logs[-1])[7:-4], v[-1][3:].split(' (')[0] if v else 'incomplete')
    else:
        r['verify'] = 'not run'
    L = os.path.join(run, 'load.log')
    if os.path.exists(L):
        ls = [float(x.split()[2]) for x in open(L) if x.split()[1:2] == ['load']]
        r['host load (mean / max)'] = '%.0f / %.0f' % (sum(ls) / len(ls), max(ls)) if ls else '-'
    else:
        r['host load (mean / max)'] = 'not recorded'
    return r


if __name__ == '__main__':
    rows = [facts(tokens.run_dir(r)) for r in sys.argv[1:]]
    keys = [k for r in rows for k in r if k != 'run']
    keys = list(dict.fromkeys(keys))
    w = max(len(k) for k in keys) + 2
    cw = [max(len(r['run']), *(len(str(r.get(k, ''))) for k in keys)) + 2 for r in rows]
    print(' ' * w + ''.join(r['run'].ljust(c) for r, c in zip(rows, cw)))
    for k in keys:
        print(k.ljust(w) + ''.join(str(r.get(k, '-')).ljust(c) for r, c in zip(rows, cw)))
