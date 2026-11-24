"""The swiftpaxos kit (notes/dsv-swiftpaxos.md): its etc/goose.py project and etc/gen-init.py
configuration (format: etc/dsv/README.md)."""
import os

# etc/goose.py's project dsv-swiftpaxos (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-swiftpaxos",
    # dsverify-lab's swiftpaxos kit (notes/dsv-swiftpaxos.md; notes/dsverify-net-port-plan.md,
    # phase 6): the lab's fork of imdea-software/swiftpaxos (examples/swiftpaxos/fork/swiftpaxos
    # at lab master 915f964, fork 66dfc21, run swift-n2nofast-1), the system's packages with its
    # kit ported onto examples/lib/remote, `examples/dsverify/swiftpaxos` (a Go module of its
    # own, module path the fork's). Into the part `Dsverify/`, with remote, `net` and the
    # net/rpc and net/http models the part `Net/`'s (std_models), lintest, porcupine, bufio and
    # encoding/hex and encoding/json (its model's names, J1 of mit-pdos/etcd-grove#24) the main
    # tree's. Names and types only, in the part (no model yet: their
    # specs are the proof's hypotheses): encoding/gob, os/signal, github.com/google/uuid,
    # github.com/orcaman/concurrent-map (`Dsverify/Code/**.toml`). gods v1.18.1 translated as
    # project dsv-epaxos translates it (the same files: the red-black tree's iterator Next/Prev
    # names only); its treemap's specs are hypotheses here too.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "swiftpaxos"),
    root="Dsverify",
    lean_roots=["github.com/imdea-software/swiftpaxos=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "github.com/emirpasic/gods=Dsverify", "github.com/google/uuid=Dsverify",
                "github.com/orcaman/concurrent-map=Dsverify", "encoding/gob=Dsverify",
                "os/signal=Dsverify",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall=",
                "bufio=", "encoding/hex=", "encoding/json=", "net/url=", "path=", "crypto/tls=", "vendor=Net",
                "golang.org/x/net/http/httpguts=Net", "go/token=Net"],
    packages=["github.com/emirpasic/gods/utils", "github.com/emirpasic/gods/containers",
              "github.com/emirpasic/gods/maps", "github.com/emirpasic/gods/trees",
              "github.com/emirpasic/gods/trees/redblacktree",
              "github.com/emirpasic/gods/maps/treemap", "github.com/google/uuid", "github.com/orcaman/concurrent-map", "encoding/gob",
              "os/signal",
              "./rpc", "./dlog", "./config", "./state", "./hook", "./replica/defs", "./replica",
              "./client", "./swift", "./master", "./examples/swiftnet",
              "./examples/swiftnet/cmd/orch"]
             + ["./examples/swiftnet/cmd/client%d" % c for c in range(6)]
             + ["./examples/swiftnet/cmd/server%d" % s for s in range(1, 7)],
    owned=[os.path.join("github_com", "imdea_software"), os.path.join("github_com", "emirpasic"),
           os.path.join("github_com", "google", "uuid"), os.path.join("github_com", "orcaman"),
           os.path.join("encoding", "gob"), os.path.join("os", "signal")],
    std_models=["net/rpc", "net/http", "encoding/json"],
    # gods v1.18.1 from its model, models/gods (gods' code but the red-black tree iterator's
    # Next/Prev, rewritten without goto: models/README.md), so that the iterator is translated
    # and gods' treemap specs are proved (notes/gods-verified.md)
    module_models={"github.com/emirpasic/gods": "models/gods"},
)

# etc/gen-init.py: gods' packages and the fork's packages whose initializers keep nothing for the
# node (generated `Init.lean`, over each package's hand-written `Base.lean`). Not here: `client`,
# `swift`, `concurrent-map`, the kit and its programs, whose first initialization hands the node's
# boot thread owned resources (the mutable globals `swift.MaxDescRoutines`, `useFastAckPool`,
# `concurrent-map`'s `SHARD_COUNT`, and `client`'s node ghost: `swift.mutGlobalsInit`,
# `client.freshAt`), which Perennial's `wp_initialize'` cannot return: their initializations are
# the lab's hand-written first-run proofs (`examples/swiftnet/InitFirst.lean`; notes/dsv-swiftpaxos.md).
SWIFT = 'github_com.imdea_software.swiftpaxos'
SWIFT_NODES = ['orch'] + [f'client{c}' for c in range(6)] + [f'server{s}' for s in range(1, 7)]
# the 13 commands' package tables (`PkgTable.lean`: the `GetIsPkgInitProp` facts their boots use;
# notes/dsv-swiftpaxos.md, "State (twelfth session)", the boot); each imports the command's
# hand-written `Init.lean`
PROGRAMS = {f'{SWIFT}.examples.swiftnet.cmd.{n}':
            f'Proof/github_com/imdea_software/swiftpaxos/examples/swiftnet/cmd/{n}/PkgTable.lean'
            for n in SWIFT_NODES}
PKGS = [f'github_com.emirpasic.gods.{p}' for p in
        ['utils', 'containers', 'maps', 'trees', 'trees.redblacktree', 'maps.treemap']] + \
    [f'{SWIFT}.{p}' for p in ['rpc', 'dlog', 'config', 'state', 'hook', 'replica.defs', 'replica',
                              'master']]
# the main tree's packages the part's closure adds to `NET_MAIN` (bufio, encoding/hex,
# encoding/json, and net/http's); encoding/json's `wp_initialize'` is proved (J1,
# mit-pdos/etcd-grove#24), no longer an `InitHyp`
MAIN = ['bufio', 'encoding.hex', 'encoding.json', 'path', 'internal.bytealg', 'net.url', 'crypto.tls']
MAIN_GEN = ['bufio', 'encoding.hex', 'encoding.json']
# initializers that are hypotheses of the part's proofs (the `InitHyp` class of their hand-written
# `Init.lean`; notes/dsv-swiftpaxos.md, "Hypotheses"): net/rpc's and net/http's (`Net/`'s models,
# as dsv-epaxos), os/signal (dsv-rabia's), and the
# names-only encoding/gob, github.com/google/uuid. Their imports: all (the default;
# dsv-inithyp-fix): net/rpc's and net/http's well-formedness conditions are
# `build_get_is_pkg_init_wf`, over every package their initializers reach, so the programs' tables
# hold that closure. Not math/rand: the boot uses `Dsverify/Proof/math/rand/Init.lean`'s `InitHyp`,
# a premise of the statement, by hand.
HYP_INITS = ['net.rpc', 'net.http', 'os.signal', 'encoding.gob',
             'github_com.google.uuid']


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL, newvars_cfg, FIN_PRE = {}, g.newvars_cfg, g.FIN_PRE
    SPECIAL[f'{SWIFT}.dlog'] = dict(
        doc='''Its fact is `True`. Its initializer initializes its imports, allocates `DLOG` and stores
`false`.''',
        alloc_types={'DLOG': 'Bool'})
    SPECIAL[f'{SWIFT}.replica.defs'] = dict(
        doc='''Its fact is `LatencyConf ↦□ ""` (no code writes it). Its initializer initializes its
imports, allocates `LatencyConf`, `Storage` and `StoreFilname` and stores their string constants.''',
        alloc_types={'LatencyConf': 'GoString', 'Storage': 'GoString', 'StoreFilname': 'GoString'},
        finish=['ipersist HLatencyConf', 'iframe Hown', 'is_pkg_init_finish'])
    SPECIAL[f'{SWIFT}.replica'] = newvars_cfg(dict(
        doc='''Its fact (`Base.lean`): its two error variables hold their `errors.New` errors for
good (`errors.newVar`; `NewQuorumSystem` compares with them). Its initializer initializes its
imports, allocates them and runs their translated initializers (`quorum.go`: `errors.New`
calls).''',
        finish=['ipersist HNO_QUORUM_FILE', 'ipersist HTHREE_QUARTERS'] + FIN_PRE + [
            'iunfold _root_.Perennial.errors.newVar',
            'isplitl []', '· iexists _; iframe #', '· iexists _; iframe #']),
        ['NO_QUORUM_FILE', 'THREE_QUARTERS'])
    for x in ['NO_QUORUM_FILE', 'THREE_QUARTERS']:
        SPECIAL[f'{SWIFT}.replica']['before'][x] = [
            'try wp_auto',
            f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{x} ⟨#F{x}, #M{x}⟩']
    return SPECIAL

# etc/dsv/kitgen.py (notes/dsv-kitgen.md): the first-run boot's tables, `BootTable.lean` and
# `BootCmdsLinked.lean` (formerly etc/dsv/_swiftpaxos_boot.py's); the machines are listed for their
# order only (the commands' mains stay as they are: server1's doc is its own)
KITGEN = dict(
    name='swiftpaxos',
    go_mains=False,
    lean_pkg=f'{SWIFT}.examples.swiftnet',
    proof_roots=[SWIFT],  # the kit's own Lean trees (kitgen --export-challenge)
    # the net/rpc model's codec (models/net/rpc/rpcgen.py; examples/swiftnet/gen-rpc.sh)
    codecs=[('rpc', 'examples/dsverify/swiftpaxos/examples/swiftnet/rpc.toml',
             'examples/dsverify/swiftpaxos/examples/swiftnet', 'swiftnet')],
    roles=[dict(cmd='orch'), dict(cmd='client{id}', ids=list(range(6))),
           dict(cmd='server{id}', ids=list(range(1, 7)))],
    boot=dict(
        # the table: server2's chain (etc/gen-init.py's cmd/server2/PkgTable.lean)
        table='server2',
        owned=[f'{SWIFT}.examples.swiftnet', f'{SWIFT}.swift', 'github_com.orcaman.concurrent_map',
               f'{SWIFT}.client', 'net.rpc', 'net.http'],
        table_doc='''The package facts of the SwiftPaxos kit's boot (notes/dsv-swiftpaxos.md, "State (thirteenth
session)", the boot): generic in a program's table `G` that gives every package of `swiftnet`'s
import closure its `isPkgInit` (`KitG G`), the facts at `G` (`wf_*`) and, for the packages whose
closure avoids the kit's owned packages (`ownedPkgs`: those whose first initialization the boot
proves, and net/rpc's and net/http's, `RpcFirstInit`), at `gOff S G` for `S` a sub-list of
`ownedPkgs` (`wfO_*`): the table in which the packages of `S` are not initialized yet.''',
        cmds_doc='''The SwiftPaxos kit's thirteen commands' boots (notes/dsv-swiftpaxos.md, "State (thirteenth
session)", the boot): each command's initialization from the machine's empty package state, its
first, through `swiftnet`'s (`BootLinked.lean`, `boot_swiftnet`), at the command's table
(`getIsPkgInit`, its `PkgTable.lean`; `kitG`).''',
        opens=['open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv',
               f'open {SWIFT} {SWIFT}.examples.swiftnet'],
        attributes=['attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp',
                    '  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256'],
        gf='netDistGF',
        variables='''variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [package_sem : cmd.{n}.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [log.Assumptions] [net.http.Assumptions]
variable [math.rand.InitHyp netDistGF] [net.rpc.InitHyp netDistGF] [net.http.InitHyp netDistGF]
variable [encoding.gob.InitHyp netDistGF]
variable [os.signal.InitHyp netDistGF] [github_com.google.uuid.InitHyp netDistGF]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF] [RpcFirstInit (GF := netDistGF)]''',
        returns="returns the machine's boot resources.",
        q='bootRes',
        post='        isPkgInit (PROP := IProp netDistGF) pkg_id.{pkg}.cmd.{n} ∗ bootRes',
    ),
)
