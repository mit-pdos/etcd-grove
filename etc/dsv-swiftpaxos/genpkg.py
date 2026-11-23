#!/usr/bin/env python3
"""Regenerate Base.lean's SwiftNetPkgState section (fields + instances in import order)."""
import os, re
R = '/shared/etcd-grove-dsvswiftpaxos'
B = R + '/Dsverify/Proof/github_com/imdea_software/swiftpaxos/Base.lean'
SW = 'github_com.imdea_software.swiftpaxos'
# (field, pkg_id suffix, doc)
PK = [
 ('utils', 'github_com.emirpasic.gods.utils', '`github.com/emirpasic/gods/utils`'),
 ('containers', 'github_com.emirpasic.gods.containers', '`github.com/emirpasic/gods/containers`'),
 ('maps', 'github_com.emirpasic.gods.maps', '`github.com/emirpasic/gods/maps`'),
 ('trees', 'github_com.emirpasic.gods.trees', '`github.com/emirpasic/gods/trees`'),
 ('redblacktree', 'github_com.emirpasic.gods.trees.redblacktree', '`github.com/emirpasic/gods/trees/redblacktree`'),
 ('treemap', 'github_com.emirpasic.gods.maps.treemap', '`github.com/emirpasic/gods/maps/treemap`'),
 ('concurrent_map', 'github_com.orcaman.concurrent_map', '`github.com/orcaman/concurrent-map` (names only)'),
 ('uuid', 'github_com.google.uuid', '`github.com/google/uuid` (names only)'),
 ('gob', 'encoding.gob', '`encoding/gob` (names only)'),
 ('signal', 'os.signal', '`os/signal` (names only)'),
 ('bytealg', 'internal.bytealg', '`internal/bytealg`'),
 ('crypto_tls', 'crypto.tls', '`crypto/tls`'),
 ('hex', 'encoding.hex', '`encoding/hex`'),
 ('json', 'encoding.json', '`encoding/json`'),
 ('token', 'go.token', '`go/token` (the net/rpc model\'s trusted `IsExported`)'),
 ('path', 'path', '`path`'),
 ('textproto', 'net.textproto', '`net/textproto` (names only, the part `Net/`\'s)'),
 ('httpguts', 'vendor.golang_org.x.net.http.httpguts', '`golang.org/x/net/http/httpguts` (names only)'),
 ('nethttp', 'net.http', '`net/http` (the model\'s)'),
 ('netrpc', 'net.rpc', '`net/rpc` (the model\'s)'),
] + [(n, SW + '.' + p, '`github.com/imdea-software/swiftpaxos/' + p.replace('.', '/') + '`') for n, p in [
 ('rpc', 'rpc'), ('dlog', 'dlog'), ('config', 'config'), ('state', 'state'), ('hook', 'hook'),
 ('defs', 'replica.defs'), ('replica', 'replica'), ('client', 'client'), ('swift', 'swift'), ('master', 'master')]]
def codefile(pid):
    rel = pid.replace('.', '/') + '.lean'
    for root in ['Dsverify/Code/', 'Net/Code/', 'Code/', '.lake/packages/perennial/Perennial/Code/']:
        if os.path.exists(R + '/' + root + rel): return R + '/' + root + rel
    return None
def deps(pid):
    f = codefile(pid)
    if not f: return set()
    t = open(f).read()
    # also chunks
    for c in re.findall(r'^public import ([\w.]+)', t, re.M):
        pass
    mods = re.findall(r'^public import ([\w.]+)', t, re.M)
    ds = set()
    for m in mods:
        for pre in ('Dsverify.Code.', 'Net.Code.', 'Perennial.Code.', 'Code.'):
            if m.startswith(pre):
                ds.add(m[len(pre):])
    return ds
pids = [p for _, p, _ in PK]
order = []
seen = set()
def visit(p):
    if p in seen: return
    seen.add(p)
    for d in sorted(deps(p)):
        if d in pids: visit(d)
    order.append(p)
for p in pids: visit(p)
byp = {p: (n, doc) for n, p, doc in PK}
fields = ''.join(f'  /-- {byp[p][1]}\'s package-level state -/\n  {byp[p][0]} : IProp GF\n' for p in order)
inst = ''
for p in order:
    n = byp[p][0]
    inst += f'''
instance {n}_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.{p} :=
  define_is_pkg_init (pkgState.{n})
instance {n}_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.{p} :=
  build_get_is_pkg_init_wf
'''
inst += f'''
instance swiftnet_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.{SW}.examples.swiftnet :=
  define_is_pkg_init iprop(True)
instance swiftnet_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.{SW}.examples.swiftnet :=
  build_get_is_pkg_init_wf
'''
s = open(B).read()
a = s.index('/-- The run\'s choice of each package')
b = s.index('end defs')
body = '''/-- The run's choice of each package's own post-initialization predicate (`isPkgInitDef`:
its package-level state), for the kit's packages and the packages they import that have no
`IsPkgInit` instance elsewhere in what this part imports (the lab's `SwiftNetPkgState`, widened).
The library hypotheses' representation predicates are its `SwiftLibs` part. -/
class SwiftNetPkgState (GF : BundledGFunctors) extends SwiftLibs GF where
''' + fields + '''
/-- A choice of `SwiftNetPkgState` at every heap. -/
abbrev SwiftNetPkgStates [GoGlobalContext] :=
  ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics], SwiftNetPkgState GF
''' + inst + '\n'
s = s[:a] + body + s[b:]
open(B, 'w').write(s)
print(order)
