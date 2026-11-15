"""etc/wal-lean-remerge.py OLD: resolve a re-merge of origin/wal-int into wal-lean (notes/wal-lean-integration.md, §7): files it changed under LinuxFs/ go to their main-tree place
(3-way against the previous merged wal-int, prefix dropped), new files get the prefix dropped."""
import os, re, subprocess, sys, tempfile
OLD = sys.argv[1]  # the wal-int commit merged before


def show(rev, p):
    r = subprocess.run(['git', 'show', f'{rev}:{p}'], capture_output=True)
    return r.stdout if r.returncode == 0 else None


def dep(b):
    return re.sub(rb'\bLinuxFs([./])((?:Code|GeneratedProof|TrustedCode|ManualProof|Spec|Proof|GooseLang)\b)', rb'\2', b)


TESTER = (b'github_com/mit_pdos/etcd_grove/examples/etcd/wal', b'github_com/mit_pdos/etcd_grove/examples/lib/durable')
changed = subprocess.run(['git', 'diff', '--name-status', OLD, 'origin/wal-int', '--', 'LinuxFs'],
                         capture_output=True, text=True).stdout.split('\n')
for line in changed:
    if not line.strip():
        continue
    st, f = line.split('\t')[0], line.split('\t')[-1]
    m = f[len('LinuxFs/'):]
    if any(t.decode() in m for t in TESTER):
        m = 'WalTester/' + m
    theirs = dep(show('origin/wal-int', f))
    if st == 'A':
        open(m, 'wb').write(theirs)
        subprocess.run(['git', 'add', '--', m])
        print('added', m)
        continue
    base = dep(show(OLD, f))
    ours = open(m, 'rb').read() if os.path.exists(m) else show('HEAD', m)
    with tempfile.TemporaryDirectory() as d:
        for n, c in (('o', ours), ('b', base), ('t', theirs)):
            open(os.path.join(d, n), 'wb').write(c)
        r = subprocess.run(['git', 'merge-file', '-p', os.path.join(d, 'o'), os.path.join(d, 'b'),
                            os.path.join(d, 't')], capture_output=True)
    open(m, 'wb').write(r.stdout)
    print('merged', m, 'conflicts' if r.returncode else 'clean')
    if r.returncode == 0:
        subprocess.run(['git', 'add', '--', m])
    if os.path.exists(f):
        subprocess.run(['git', 'rm', '-q', '-f', '--', f])
