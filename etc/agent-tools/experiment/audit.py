#!/usr/bin/env python3
"""Audit a challenge agent's transcript for looks at the original proofs.

usage: audit.py TRANSCRIPT.jsonl RUN_DIR     (prints one JSON line)
Flags every tool call whose input mentions a forbidden location: the answers, the exported
btree sources, the btree worktree, git, other runs, the main repository.
"""
import json, sys, os, re

tr, run = sys.argv[1], sys.argv[2]
FORBID = [r'/exp/answers', r'btree-src', r'worktrees/btree', r'\bgit\b', r'worktree-btree',
          r'/exp/runs/(?!' + re.escape(os.path.basename(run)) + r')', r'/exp/tracks', r'/home/ubuntu/etcd-grove(?!/\.claude/worktrees/no-wp-auto/\.lake)',
          r'\.claude-csail', r'/home/ubuntu/perennial', r'github\.com']
hits = []
calls = 0
for line in open(tr):
    try:
        m = json.loads(line)
    except Exception:
        continue
    if m.get('type') != 'assistant':
        continue
    for b in m.get('message', {}).get('content', []) or []:
        if b.get('type') != 'tool_use':
            continue
        calls += 1
        s = json.dumps(b.get('input', {}))
        for pat in FORBID:
            if re.search(pat, s):
                hits.append({'tool': b.get('name'), 'pattern': pat, 'input': s[:300]})
                break
print(json.dumps({'run': os.path.basename(run), 'tool_calls': calls, 'violations': len(hits), 'hits': hits[:10]}))
