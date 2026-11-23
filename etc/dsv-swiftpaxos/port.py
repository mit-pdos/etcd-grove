#!/usr/bin/env python3
"""Copy lab modules into Dsverify/ with renamed paths and imports (mechanical first pass).
usage: port.py MODULE...   (lab module names, e.g. Spec.swift.Model.Defs); --force overwrites."""
import os, re, sys
LAB = '/shared/dsverify-lab/examples/swiftpaxos/proof'
DST = '/shared/etcd-grove-dsvswiftpaxos'
P = 'github_com.imdea_software.swiftpaxos'
DIRMAP = {
    'swift': P + '.swift', 'replica': P + '.replica', 'client': P + '.client',
    'defs': P + '.replica.defs', 'master': P + '.master', 'state': P + '.state',
    'rpc': P + '.rpc', 'dlog': P + '.dlog', 'hook': P + '.hook', 'config': P + '.config',
    'swiftnet': P + '.examples.swiftnet', 'pkg': P + '.pkg', 'net': P + '.netrpc',
    'gob': 'encoding.gob', 'cmap': 'github_com.orcaman.concurrent_map',
    'treemap': 'github_com.emirpasic.gods.maps.treemap', 'slices': P + '.slices',
}


def newmod(m):
    parts = m.split('.')
    if parts[0] in ('Spec', 'Proof') and len(parts) > 1 and parts[1] in DIRMAP:
        rest = ('.' + '.'.join(parts[2:])) if len(parts) > 2 else ''
        return 'Dsverify.' + parts[0] + '.' + DIRMAP[parts[1]] + rest
    if m == 'SwiftNetSpec':
        return 'Dsverify.Proof.' + P + '.Base'
    if parts[0] == 'Swift':
        return 'Dsverify.' + '.'.join(parts[1:])
    return None


IMP = re.compile(r'^((?:public )?import )([\w.]+)\n', re.M)


def port(m, force=False):
    nm = newmod(m)
    src = os.path.join(LAB, m.replace('.', '/') + '.lean')
    dst = os.path.join(DST, nm.replace('.', '/') + '.lean')
    if os.path.exists(dst) and not force:
        return dst, False
    t = open(src).read()
    dropped = []

    def rimp(mo):
        i = mo.group(2)
        if i.startswith('Harness.'):
            dropped.append(i)
            return ''
        n = newmod(i)
        return mo.group(1) + (n if n else i) + '\n'
    t = IMP.sub(rimp, t)
    t = re.sub(r'^(open .*?) NetConn\b', r'\1 Net', t, flags=re.M)
    t = re.sub(r'^(open .*?) dsverify_lab\.harness\b', r'\1', t, flags=re.M)
    if dropped:
        t = t.replace('@[expose] public section',
                      '-- PORT: lab imports dropped: ' + ', '.join(dropped) +
                      '\n\n@[expose] public section', 1)
    hdr = ('/-\nPorted from dsverify-lab examples/swiftpaxos/proof/' + m.replace('.', '/') +
           '.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).\n-/\n')
    t = hdr + t
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, 'w').write(t)
    return dst, True


if __name__ == '__main__':
    force = '--force' in sys.argv
    for m in [a for a in sys.argv[1:] if not a.startswith('--')]:
        d, w = port(m, force)
        print(('wrote ' if w else 'kept ') + d)
