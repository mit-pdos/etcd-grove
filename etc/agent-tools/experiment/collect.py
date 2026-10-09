#!/usr/bin/env python3
"""Collect the metrics of the challenge runs.

usage: collect.py [RUN...]   (default: every run in agents.json whose transcript exists)
Writes exp/results/<run>.json and prints a table.
"""
import json, os, re, shutil, subprocess, sys
from datetime import datetime

T = '/home/ubuntu/.claude/jobs/f5d25fd8/tmp'
E = T + '/exp'
TASKS = '/tmp/claude-1000/-home-ubuntu-etcd-grove/f5d25fd8-592c-42b2-acf0-0f216d3ec27b/tasks'
agents = json.load(open(E + '/runs/agents.json'))
os.makedirs(E + '/results/transcripts', exist_ok=True)

def ts(s):
    return datetime.fromisoformat(s.replace('Z', '+00:00')).timestamp()

def transcript_metrics(path):
    seen = set()
    out_tok = in_tok = cache_read = cache_write = 0
    tool_calls = 0
    first = last = None
    for line in open(path):
        try:
            m = json.loads(line)
        except Exception:
            continue
        t = m.get('timestamp')
        if t:
            first = first or ts(t)
            last = ts(t)
        if m.get('type') != 'assistant':
            continue
        msg = m.get('message', {})
        for b in msg.get('content', []) or []:
            if b.get('type') == 'tool_use':
                tool_calls += 1
        mid = msg.get('id')
        if mid in seen:
            continue
        seen.add(mid)
        u = msg.get('usage', {}) or {}
        out_tok += u.get('output_tokens', 0)
        in_tok += u.get('input_tokens', 0)
        cache_read += u.get('cache_read_input_tokens', 0)
        cache_write += u.get('cache_creation_input_tokens', 0)
    return {'api_messages': len(seen), 'output_tokens': out_tok, 'input_fresh': in_tok,
            'cache_read': cache_read, 'cache_write': cache_write,
            'input_total': in_tok + cache_read + cache_write, 'tool_calls': tool_calls,
            'wall_min': round((last - first) / 60, 1) if first else None}

def tool_log(run):
    p = f'{E}/runs/{run}/.tool-log'
    calls = {}
    secs = 0.0
    if os.path.exists(p):
        for l in open(p):
            parts = l.split()
            if len(parts) < 3:
                continue
            kind = parts[1]
            try:
                s = float(parts[-2])
            except ValueError:
                s = 0.0
            calls[kind] = calls.get(kind, 0) + 1
            secs += s
    return {'tool_calls_by_kind': calls, 'checks': sum(calls.values()), 'tool_wait_min': round(secs / 60, 1)}

runs = sys.argv[1:] or list(agents)
rows = []
for run in runs:
    tr = f'{TASKS}/{agents[run]}.output'
    if not os.path.exists(tr):
        continue
    shutil.copy(tr, f'{E}/results/transcripts/{run}.jsonl')
    ch = re.match(r'(?:base|treat)-(.*)-\d+$', run).group(1)
    r = {'run': run, 'condition': run.split('-')[0], 'challenge': ch}
    r.update(transcript_metrics(tr))
    r.update(tool_log(run))
    g = json.loads(subprocess.run(['python3', '-I', T + '/bin/grade.py', f'{E}/runs/{run}', ch],
                                  capture_output=True, text=True).stdout)
    r['pass'] = g['pass']
    r['grade'] = g
    a = json.loads(subprocess.run(['python3', '-I', T + '/bin/audit.py', tr, f'{E}/runs/{run}'],
                                  capture_output=True, text=True).stdout)
    r['audit_violations'] = a['violations']
    r['audit_hits'] = a['hits']
    json.dump(r, open(f'{E}/results/{run}.json', 'w'), indent=1)
    rows.append(r)
print(f"{'run':28s} pass  out_tok  in_tok(M) msgs calls checks wait_min wall_min lines audit")
for r in rows:
    print(f"{r['run']:28s} {str(r['pass']):5s} {r['output_tokens']:7d} {r['input_total']/1e6:8.2f} {r['api_messages']:4d} "
          f"{r['tool_calls']:5d} {r['checks']:6d} {r['tool_wait_min']:8.1f} {r['wall_min']!s:>8} {r['grade']['proof_lines']:5d} {r['audit_violations']}")
