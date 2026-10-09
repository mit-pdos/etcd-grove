#!/usr/bin/env python3
"""Tier-2 run directories: runs/{base,treat}-{node__get,node__insert}-{1,2}/ with BRIEF.md."""
import os, shutil
E = '/home/ubuntu/.claude/jobs/f5d25fd8/tmp/exp'
CH = ['node__get', 'node__insert']
brief = open(E + '/CHALLENGE_BRIEF.md').read()
tools = {'base': open(E + '/TOOLS_BASELINE.md').read(), 'treat': open(E + '/TOOLS_TREATMENT.md').read()}
src = {'base': E + '/template2', 'treat': E + '/treatment-template2'}
for cond in ['base', 'treat']:
    for ch in CH:
        for rep in (1, 2):
            name = f'{cond}-{ch}-{rep}'
            d = f'{E}/runs/{name}'
            shutil.rmtree(d, ignore_errors=True)
            shutil.copytree(src[cond], d, ignore=shutil.ignore_patterns('.ide.sock', '.tool-log', '.ide.err', '.grade_*'))
            open(d + '/BRIEF.md', 'w').write(brief.replace('RUN_DIR', d).replace('CHALLENGE', ch).replace('TOOLS_SECTION', tools[cond]))
            print(name)
