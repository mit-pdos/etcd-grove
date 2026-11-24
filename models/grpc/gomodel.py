#!/usr/bin/env python3
"""Run a go command in a module with google.golang.org/grpc replaced by this model.

    models/grpc/gomodel.py DIR GOARGS...      e.g.  gomodel.py examples build ./...

The model build's go.mod is the module's own go.mod plus `replace google.golang.org/grpc =>
<this directory>`, written to a temporary directory (with the module's relative replace paths
made absolute) and passed as -modfile, so that the normal build never sees the model and the
model build cannot drift from the normal one. The go.sum is the module's (copied; the model's
requirements are grpc-go v1.84.0's, so no sum is missing).

Runs `go` from PATH with GOFLAGS=-mod=mod, GOPROXY=off unless set, and the module directory as the
working directory; exits with go's status.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

MODEL = os.path.dirname(os.path.abspath(__file__))


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    mod = os.path.abspath(sys.argv[1])
    args = sys.argv[2:]
    env = dict(os.environ)
    env.setdefault('GOPROXY', 'off')
    env.setdefault('GOFLAGS', '-mod=mod')
    env.setdefault('GOTOOLCHAIN', 'local')
    tmp = tempfile.mkdtemp(prefix='gomodel-')
    try:
        modfile = os.path.join(tmp, 'go.model.mod')
        shutil.copy(os.path.join(mod, 'go.mod'), modfile)
        if os.path.exists(os.path.join(mod, 'go.sum')):
            shutil.copy(os.path.join(mod, 'go.sum'), os.path.join(tmp, 'go.model.sum'))
        j = json.loads(subprocess.run(['go', 'mod', 'edit', '-json', modfile], env=env,
                                      check=True, capture_output=True, text=True).stdout)
        edits = []
        for r in j.get('Replace') or []:
            new = r['New']
            if not new.get('Version') and (new['Path'].startswith('./') or
                                           new['Path'].startswith('../')):
                old = r['Old']['Path'] + ('@' + r['Old']['Version'] if r['Old'].get('Version') else '')
                edits.append('-replace=%s=%s' % (old, os.path.normpath(os.path.join(mod, new['Path']))))
        edits.append('-replace=google.golang.org/grpc=' + MODEL)
        subprocess.run(['go', 'mod', 'edit'] + edits + [modfile], env=env, check=True)
        cmd = ['go', args[0], '-modfile=' + modfile] + args[1:]
        sys.exit(subprocess.run(cmd, cwd=mod, env=env).returncode)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == '__main__':
    main()
