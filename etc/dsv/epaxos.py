"""The EPaxos kit (notes/dsv-epaxos.md): its etc/goose.py project and etc/gen-init.py
configuration (format: etc/dsv/README.md)."""
import os

# etc/goose.py's project dsv-epaxos (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-epaxos",
    # dsverify-lab's EPaxos kit (notes/dsv-epaxos.md; notes/dsverify-net-port-plan.md, phase 6):
    # the lab's fork of imdea-software/swiftpaxos (epaxos-e1nogs-1, fork commit 71d99d4), the
    # packages the kit runs, with its kit ported onto examples/lib/remote,
    # `examples/dsverify/epaxos` (a Go module of its own, module path the fork's with
    # "-epaxos": the swiftpaxos kit translates the same repository). Into the part `Dsverify/`,
    # with gods (the real v1.18.1) translated into it too; remote, `net`, net/rpc and net/http
    # the part `Net/`'s, lintest, porcupine, bufio and encoding/json (its model's names, J1 of
    # mit-pdos/etcd-grove#24) the main tree's.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "epaxos"),
    root="Dsverify",
    lean_roots=["github.com/imdea-software/swiftpaxos-epaxos=Dsverify",
                "github.com/emirpasic/gods=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall=",
                "bufio=", "encoding/json=", "net/url=", "path=", "crypto/tls=",
                "golang.org/x/net/http/httpguts=Net", "vendor=Net", "go/token=Net"],
    packages=["github.com/emirpasic/gods/utils", "github.com/emirpasic/gods/containers",
              "github.com/emirpasic/gods/maps", "github.com/emirpasic/gods/trees",
              "github.com/emirpasic/gods/trees/redblacktree",
              "github.com/emirpasic/gods/maps/treemap",
              "./rpc", "./dlog", "./config", "./state", "./replica/defs", "./replica",
              "./epaxos", "./master", "./examples/epaxosnet", "./examples/epaxosnet/cmd/orch"]
             + ["./examples/epaxosnet/cmd/client%d" % c for c in range(10)]
             + ["./examples/epaxosnet/cmd/server%d" % s for s in range(1, 7)],
    owned=[os.path.join("github_com", "imdea_software", "swiftpaxos_epaxos"),
           os.path.join("github_com", "emirpasic")],
    std_models=["net/rpc", "net/http", "encoding/json"],
)

# etc/gen-init.py: gods' packages, the fork's, the kit's and its 17 programs
EPAXOS = 'github_com.imdea_software.swiftpaxos_epaxos'
EPAXOS_NODES = ['orch'] + [f'client{c}' for c in range(10)] + [f'server{s}' for s in range(1, 7)]
PKGS = [f'github_com.emirpasic.gods.{p}' for p in
        ['utils', 'containers', 'maps', 'trees', 'trees.redblacktree', 'maps.treemap']] + \
    [f'{EPAXOS}.{p}' for p in ['rpc', 'dlog', 'config', 'state', 'replica.defs', 'replica',
                               'epaxos', 'master', 'examples.epaxosnet']] + \
    [f'{EPAXOS}.examples.epaxosnet.cmd.{n}' for n in EPAXOS_NODES]
PROGRAMS = {f'{EPAXOS}.examples.epaxosnet.cmd.{n}':
            f'Proof/{EPAXOS.replace(".", "/")}/examples/epaxosnet/cmd/{n}/PkgTable.lean'
            for n in EPAXOS_NODES}
# the main tree's packages the part's closure adds to `NET_MAIN` (EPaxos: bufio, encoding/json
# and net/http's)
MAIN = ['bufio', 'encoding.json', 'path', 'internal.bytealg', 'net.url', 'crypto.tls']
# of which the part gets a copy of the main tree's `Init.lean` (over the part's `PkgInitExt`):
# encoding/json's `wp_initialize'` is proved (J1, mit-pdos/etcd-grove#24), no longer an `InitHyp`
MAIN_GEN = ['bufio', 'encoding.json']
# initializers that are hypotheses of the part's proofs (notes/dsv-epaxos.md, "Hypotheses"; the
# `InitHyp` class): net/rpc's and net/http's (`Net/`'s models: no initializer proof; their closure
# reaches untranslated initializers)
HYP_INITS = ['net.rpc', 'net.http']
# their imports: all (the default; dsv-inithyp-fix): each `Init.lean`'s well-formedness condition
# is `build_get_is_pkg_init_wf`, over every package its initializer reaches (net/http's closure's
# packages without a fact elsewhere have a `True` one in the part, `Dsverify/Proof/<pkg>/Base.lean`),
# so the programs' tables hold that closure


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL, newvars_cfg, DSV_EPAXOS = {}, g.newvars_cfg, EPAXOS
    SPECIAL[f'{DSV_EPAXOS}.dlog'] = dict(
        doc='''Its fact is `True`. Its initializer initializes its imports, allocates `DLOG` and stores
`false`.''',
        alloc_types={'DLOG': 'Bool'})
    SPECIAL[f'{DSV_EPAXOS}.replica.defs'] = dict(
        doc='''Its fact is `LatencyConf ↦□ ""` (no code writes it). Its initializer initializes its
imports, allocates `LatencyConf`, `Storage` and `StoreFilname` and stores their string constants.''',
        alloc_types={'LatencyConf': 'GoString', 'Storage': 'GoString', 'StoreFilname': 'GoString'},
        finish=['ipersist HLatencyConf', 'iframe Hown', 'is_pkg_init_finish'])
    SPECIAL[f'{DSV_EPAXOS}.replica'] = newvars_cfg(dict(
        doc='''Its fact is `True`. Its initializer initializes its imports, allocates its two error
variables and runs their translated initializers (`quorum.go`: `errors.New` calls).'''),
        ['NO_QUORUM_FILE', 'THREE_QUARTERS'])
    SPECIAL[f'{DSV_EPAXOS}.epaxos'] = newvars_cfg(dict(
        doc='''Its fact is `True`. Its initializer initializes its imports, allocates
`errVarintOverflow` (an `errors.New` call, `varint.go`) and `deferMap` (`make(map[uint64]uint64)`,
`epaxos.go`) and runs their translated initializers.''',
        alloc_types={'deferMap': 'GoMap'}), ['errVarintOverflow'])
    SPECIAL[f'{DSV_EPAXOS}.epaxos']['before']['errVarintOverflow'] = [
        'try wp_auto', 'wp_apply (wp_map_make1 (K := w64) (V := w64) go.uint64 go.uint64) as %mdm Hdm',
        'try wp_auto'] + SPECIAL[f'{DSV_EPAXOS}.epaxos']['before']['errVarintOverflow']
    return SPECIAL
