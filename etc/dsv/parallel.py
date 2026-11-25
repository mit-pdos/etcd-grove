#!/usr/bin/env python3
"""Parallelism of a run, from its transcripts: when each subagent ran, how many ran at once, and
how long the main session sat idle waiting (a `sleep`/`until` poll) while no subagent was running.

  etc/dsv/parallel.py [-v] RUN...      (as root; RUN as for tokens.py: a name under $DSV_LAB/runs, or a path)

Per run: (-v) the subagents' working spans (start, end, minutes; an agent continued by a message
later is split at gaps of 5+ minutes), then the minutes with 0, 1, 2-3 and 4+
subagents running, the mean number running, and the minutes the main session spent in polling
shell commands (`sleep N`, `until ...; do sleep`) while every subagent had already finished.
Times are minutes from the run's first transcript line; pauses of 30+ minutes with no transcript
line anywhere are left out, as in compare.py.
"""
import json, os, re, sys
from datetime import datetime
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tokens import run_dir

def ts(s):
    return datetime.fromisoformat(s.replace('Z', '+00:00')).timestamp()

def lines(path):
    with open(path, errors='replace') as f:
        for l in f:
            try: yield json.loads(l)
            except ValueError: pass

def run(R, verbose):
    P = os.path.join(R, 'home/.claude/projects')
    mains, subs = [], []
    for d, _, fs in os.walk(P):
        for f in fs:
            if f.endswith('.jsonl'):
                (subs if 'subagents' in d else mains).append(os.path.join(d, f))
    # descriptions and models from the main sessions' Agent calls, keyed by the tool_use id
    desc = {}
    events = []          # every transcript timestamp, for the pause rule
    polls = []           # (start, end) of the main session's polling shell commands
    pending = {}
    for m in mains:
        for o in lines(m):
            t = o.get('timestamp')
            if not t: continue
            t = ts(t); events.append(t)
            msg = o.get('message') or {}
            for c in msg.get('content') or [] if isinstance(msg.get('content'), list) else []:
                if c.get('type') == 'tool_use':
                    i = c.get('input') or {}
                    if c.get('name') in ('Agent', 'Task'):
                        desc[c['id']] = (i.get('description', ''), i.get('model', ''))
                    elif c.get('name') == 'Bash':
                        cmd = i.get('command', '')
                        if re.search(r'\bsleep\s+\d|until .*;\s*do\s+sleep', cmd):
                            pending[c['id']] = t
                elif c.get('type') == 'tool_result' and c.get('tool_use_id') in pending:
                    polls.append((pending.pop(c['tool_use_id']), t))
    spans = []
    for s in subs:
        tt = sorted(ts(o['timestamp']) for o in lines(s) if o.get('timestamp'))
        if not tt: continue
        events += tt
        name = os.path.basename(s)[:-6]
        # an agent continued later (a message sent to it) is idle in between: split at 5-minute gaps
        a = tt[0]
        for x, y in zip(tt, tt[1:]):
            if y - x > 300: spans.append((a, x, name)); a = y
        spans.append((a, tt[-1], name))
    if not events: return None
    # the active clock: drop gaps of 30+ minutes with no transcript line
    events.sort()
    gaps = [(a, b) for a, b in zip(events, events[1:]) if b - a >= 1800]
    t0 = events[0]
    def act(t):
        return (t - t0 - sum(min(b, t) - a for a, b in gaps if a < t)) / 60
    end = act(events[-1])
    # minute-by-minute count of running subagents
    n = int(end) + 1
    count = [0] * n
    for a, b, _ in spans:
        for k in range(int(act(a)), min(n, int(act(b)) + 1)): count[k] += 1
    busy = lambda k: count[k] > 0
    idle_poll = 0
    for a, b in polls:
        for k in range(int(act(a)), min(n, int(act(b)))):
            if not busy(k): idle_poll += 1
    hist = {'0': sum(c == 0 for c in count), '1': sum(c == 1 for c in count),
            '2-3': sum(2 <= c <= 3 for c in count), '4+': sum(c >= 4 for c in count)}
    print(f'== {os.path.basename(R.rstrip("/"))}: {end:.0f} active min, {len(set(x[2] for x in spans))} subagents, {len(spans)} working spans')
    if verbose:
        for a, b, name in sorted(spans):
            print(f'   {act(a):5.0f} {act(b):5.0f} {(b - a) / 60:5.0f}m  {name}')
    print('   minutes with 0 / 1 / 2-3 / 4+ subagents running: '
          f"{hist['0']} / {hist['1']} / {hist['2-3']} / {hist['4+']}")
    print(f'   mean running: {sum(count) / n:.2f}; main session polling with no subagent running: '
          f'{idle_poll} min; polls: {len(polls)}, {sum(b - a for a, b in polls) / 60:.0f} min in all')
    return hist

if __name__ == '__main__':
    args = sys.argv[1:]
    v = '-v' in args
    for R in [a for a in args if a != '-v']:
        run(run_dir(R), v)
