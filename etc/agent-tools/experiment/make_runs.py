#!/usr/bin/env python3
"""Create the run directories: runs/{base,treat}-{challenge}-{rep}/ with BRIEF.md."""
import os, shutil, sys
E = '/home/ubuntu/.claude/jobs/f5d25fd8/tmp/exp'
CH = ['items__insertAt', 'items__find', 'node__split']
REPS = int(sys.argv[1]) if len(sys.argv) > 1 else 2
brief = open(E + '/CHALLENGE_BRIEF.md').read()
tools = {'base': open(E + '/TOOLS_BASELINE.md').read(), 'treat': open(E + '/TOOLS_TREATMENT.md').read()}
src = {'base': E + '/template', 'treat': E + '/treatment-template'}
os.makedirs(E + '/runs', exist_ok=True)
for cond in ['base', 'treat']:
    for ch in CH:
        for rep in range(1, REPS + 1):
            name = f'{cond}-{ch}-{rep}'
            d = f'{E}/runs/{name}'
            if os.path.exists(d):
                shutil.rmtree(d)
            shutil.copytree(src[cond], d, ignore=shutil.ignore_patterns('.ide.sock', '.tool-log', '.ide.err', '.grade_*'))
            b = brief.replace('RUN_DIR', d).replace('CHALLENGE', ch).replace('TOOLS_SECTION', tools[cond])
            open(d + '/BRIEF.md', 'w').write(b)
            print(name)
