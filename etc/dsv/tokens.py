#!/usr/bin/env python3
# Usage: etc/dsv/tokens.py [--json] RUN... (as root: the transcripts are the container's): token usage
# per run from its transcripts (main session + subagents), counting each API response once (a response
# is split over several transcript lines sharing message.id). --json: one object per run, with the
# active minutes and the pauses. RUN: a run's name, $DSV_LAB/runs/RUN, or the path of a run's directory
# (anything with a /).
import json, glob, sys, os
from datetime import datetime, timedelta
from collections import Counter

def run_dir(a):
    """The directory of the run RUN: a path (with a /) as given, else $DSV_LAB/runs/RUN."""
    if '/' in a: return a
    lab = os.environ.get('DSV_LAB')
    if not lab: sys.exit('set DSV_LAB to the experiment directory, or give the run as a path')
    return os.path.join(lab, 'runs', a)


K = ['input_tokens', 'cache_creation_input_tokens', 'cache_read_input_tokens', 'output_tokens']


def transcripts(run):
    """(path, 'main' | 'subagents') for every transcript of the run."""
    P = os.path.join(run, 'home/.claude/projects')
    return ([(f, 'main') for f in glob.glob(P + '/*/*.jsonl')] +
            [(f, 'subagents') for f in glob.glob(P + '/*/*/subagents/*.jsonl')])


PAUSE = 30   # minutes with no line in any transcript: the run was stopped (a usage limit, a closed session)


def clock(run, pause=PAUSE):
    """(t0, minutes, pauses): minutes(t) is active time since the run's first transcript line, pauses
    (gaps of more than `pause` minutes in every transcript at once) left out; pauses is [(start, end)]."""
    ts = sorted(datetime.fromisoformat(e['timestamp'].replace('Z', '+00:00'))
                for f, _ in transcripts(run) for e in map(json.loads, open(f)) if e.get('timestamp'))
    if not ts: return None, None, []
    gaps = [(a, b) for a, b in zip(ts, ts[1:]) if b - a > timedelta(minutes=pause)]
    def minutes(t):
        off = sum(((min(t, b) - a).total_seconds() for a, b in gaps if t > a), 0.0)
        return ((t - ts[0]).total_seconds() - off) / 60
    return ts[0], minutes, gaps


def usage(run):
    """{'main': Counter, 'subagents': Counter, 'all': Counter, 'responses', 'models', 'start', 'end'}"""
    tot = {'main': Counter(), 'subagents': Counter()}; models = Counter(); seen = set(); ts = []
    for f, who in transcripts(run):
        for l in open(f):
            e = json.loads(l)
            if e.get('timestamp'): ts.append(e['timestamp'])
            m = e.get('message') or {}
            if e.get('type') != 'assistant' or 'usage' not in m: continue
            key = m.get('id') or e.get('requestId') or e.get('uuid')
            if key in seen: continue
            seen.add(key); u = m['usage']
            for k in K: tot[who][k] += u.get(k) or 0
            models[m.get('model')] += 1
    tot['all'] = tot['main'] + tot['subagents']
    tot.update(responses=len(seen), models=dict(models), start=min(ts) if ts else None, end=max(ts) if ts else None)
    return tot


def stats(run):
    """usage(run) plus the active minutes (pauses left out) and the pauses, as JSON-ready values."""
    u = usage(run)
    t0, minutes, gaps = clock(run)
    end = datetime.fromisoformat(u['end'].replace('Z', '+00:00')) if u['end'] else None
    return {'run': os.path.basename(run.rstrip('/')), 'start': u['start'], 'end': u['end'],
            'active_min': round(minutes(end), 1) if end else None,
            'pauses': [[a.isoformat(), b.isoformat()] for a, b in gaps],
            'responses': u['responses'], 'models': u['models'],
            'tokens': {who: dict(u[who]) | {'total': sum(u[who].values())} for who in ('main', 'subagents', 'all')}}


if __name__ == '__main__':
    if sys.argv[1:2] == ['--json']:
        for run in map(run_dir, sys.argv[2:]):
            print(json.dumps(stats(run), indent=1))
        sys.exit(0)
    for run in map(run_dir, sys.argv[1:]):
        u = usage(run)
        print('== %s  (%s .. %s, %d responses, models %s)' % (os.path.basename(run.rstrip('/')),
              (u['start'] or '')[:16], (u['end'] or '')[:16], u['responses'], u['models']))
        print('   %-10s %12s %14s %14s %10s %14s' % ('', 'input', 'cache write', 'cache read', 'output', 'total'))
        for who in ('main', 'subagents', 'all'):
            c = u[who]
            print('   %-10s %12s %14s %14s %10s %14s' % (who, *['{:,}'.format(c[k]) for k in K], '{:,}'.format(sum(c.values()))))
