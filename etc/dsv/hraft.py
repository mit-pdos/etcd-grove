"""The hraft kit (notes/dsv-hraft.md; the plan: mit-pdos/etcd-grove#48): its etc/goose.py project
and etc/gen-init.py configuration (format: etc/dsv/README.md): hashicorp/raft's package, the
snapshot store and the kit `examples/hraftnet` with its twelve machines' commands (stage S1: the
kit translated, with the generated initializers; no proofs of the kit yet)."""
import os

# etc/goose.py's project dsv-hraft (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-hraft",
    # dsverify-lab's hraft-4 verification fork of hashicorp/raft v1.8.0 (examples/hraft/fork/raft
    # at lab c39f136, fork commit 02f88d5 on v1.8.0 0f543c0), without the lab's in-process harness,
    # `examples/dsverify/hraft` (a Go module of its own, module path the fork's), with the kit
    # `examples/hraftnet` on examples/lib/remote. Into the part `Dsverify/`, with remote, `net`,
    # `net/rpc` and `net/http` the part `Net/`'s (the models: std_models), lintest and porcupine
    # the main tree's (craq's roots). The fork needs only the standard library and goose's
    # `primitive`; the kit adds net/rpc (Net's model) and remote.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "hraft"),
    root="Dsverify",
    lean_roots=["github.com/hashicorp/raft=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove/examples/lib/durable=Dsverify",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall=",
                "bufio=", "net/url=", "path=", "crypto/tls=", "vendor=Net",
                "golang.org/x/sys=", "path/filepath=", "internal/filepathlite=",
                "golang.org/x/net/http/httpguts=Net", "go/token=Net"],
    packages=[".", "./examples/snapstore", "./examples/hraftnet/rpctransport",
              "./examples/hraftnet/service", "./examples/hraftnet", "./examples/hraftnet/cmd/orch"]
             + ["./examples/hraftnet/cmd/client%d" % c for c in range(5)]
             + ["./examples/hraftnet/cmd/server%d" % s for s in range(1, 7)]
             # hraft_robust (notes/dsv-hraft.md): the durable stores and the restartable servers
             + ["./examples/hraftnet/disk", "./examples/hraftnet/rserver"]
             + ["./examples/hraftnet/cmd/rserver%d" % s for s in range(1, 7)],
    owned=[os.path.join("github_com", "hashicorp")],
    std_models=["net/rpc", "net/http"],
)

# etc/gen-init.py: raft's package, the snapshot store, the kit and its twelve machines' commands.
# net/rpc's and net/http's initializers are `Net/`'s (external; their `wp_initialize'` and first-run
# `wp_init_first` Net's interim axioms, `etc/gen-init.py`'s `NET_AXIOM_INITS`), as craq's
HRAFT = 'github_com.hashicorp.raft'
# (hraft_robust R3) `examples/lib/durable`, translated with its bodies into the part (the kit's own
# translation of a package the main tree keeps trusted): its configuration is WalTester's
_DURABLE = 'github_com.mit_pdos.etcd_grove.examples.lib.durable'
OWN = {_DURABLE}
HRAFT_NODES = ['orch'] + [f'client{c}' for c in range(5)] + [f'server{s}' for s in range(1, 7)]
# hraft_robust: the restartable server machines' commands (`rserver.ServerR`)
HRAFT_RNODES = [f'rserver{s}' for s in range(1, 7)]
PKGS = [HRAFT, f'{HRAFT}.examples.snapstore', f'{HRAFT}.examples.hraftnet.rpctransport',
        f'{HRAFT}.examples.hraftnet.service', f'{HRAFT}.examples.hraftnet',
        # hraft_robust (R3): the durable stores
        f'{HRAFT}.examples.hraftnet.disk', _DURABLE,
        # hraft_robust: the restartable server machine
        f'{HRAFT}.examples.hraftnet.rserver'] + \
    [f'{HRAFT}.examples.hraftnet.cmd.{n}' for n in HRAFT_NODES + HRAFT_RNODES]
# the twelve commands' package tables (the deployment's boots), and the restartable servers'
PROGRAMS = {f'{HRAFT}.examples.hraftnet.cmd.{n}':
            f'Proof/{HRAFT.replace(".", "/")}/examples/hraftnet/cmd/{n}/PkgTable.lean'
            for n in HRAFT_NODES + HRAFT_RNODES}
HYP_INITS = []
# the main tree's packages net/http's closure needs, added to `NET_MAIN` (as craq's)
MAIN = ['bufio', 'path', 'internal.bytealg', 'net.url', 'crypto.tls',
        # (hraft_robust R3) the bodied durable's imports that os does not import
        'internal.filepathlite', 'path.filepath']
MAIN_GEN = ['bufio']

# raft's `errors.New` package variables, with their messages (api.go, kept.go, replication.go,
# encoding.go), and snapstore's
RAFT_ERRS = dict(
    ErrLeader="node is the leader",
    ErrNotLeader="node is not the leader",
    ErrNotVoter="node is not a voter",
    ErrLeadershipLost="leadership lost while committing log",
    ErrAbortedByRestore="snapshot restored while committing log",
    ErrRaftShutdown="raft is already shutdown",
    ErrEnqueueTimeout="timed out enqueuing operation",
    ErrNothingNewToSnapshot="nothing new to snapshot",
    ErrUnsupportedProtocol="operation not supported with current protocol version",
    ErrCantBootstrap="bootstrap only works on new clusters",
    ErrLeadershipTransferInProgress="leadership transfer in progress",
    ErrIncompatibleLogStore="log store does not implement some required methods or malformed",
    ErrTransportShutdown="transport shutdown",
    ErrPipelineShutdown="append pipeline closed",
    ErrLogNotFound="log not found",
    ErrPipelineReplicationNotSupported="pipeline replication not supported",
    errShortBuffer="encoding: short buffer",
)
SNAP_ERRS = dict(ErrNoSnapshot="snapstore: no such snapshot", ErrClosed="snapstore: sink closed")
# the disk's (codec.go, disk.go, snap.go)
DISK_ERRS = dict(ErrCorrupt="disk: corrupt file", ErrNotFound="not found", ErrMissing="disk: missing file",
                 ErrNoSnapshot="disk: no such snapshot", ErrClosed="disk: sink closed")


# raft's three stable-store keys (raft.go), with the bytes they hold
RAFT_KEYS = dict(keyCurrentTerm="CurrentTerm", keyLastVoteTerm="LastVoteTerm", keyLastVoteCand="LastVoteCand")
# `RaftErr`'s constructors (`Base.lean`), in `RaftErr.all`'s order, with their variables
RAFT_ERR_CODES = dict(
    leader="ErrLeader", notLeader="ErrNotLeader", notVoter="ErrNotVoter",
    leadershipLost="ErrLeadershipLost", abortedByRestore="ErrAbortedByRestore",
    raftShutdown="ErrRaftShutdown", enqueueTimeout="ErrEnqueueTimeout",
    nothingNewToSnapshot="ErrNothingNewToSnapshot", unsupportedProtocol="ErrUnsupportedProtocol",
    cantBootstrap="ErrCantBootstrap", leadershipTransferInProgress="ErrLeadershipTransferInProgress",
    incompatibleLogStore="ErrIncompatibleLogStore", shortBuffer="errShortBuffer",
    transportShutdown="ErrTransportShutdown", pipelineShutdown="ErrPipelineShutdown",
    logNotFound="ErrLogNotFound", pipelineReplicationNotSupported="ErrPipelineReplicationNotSupported")


def raft_cfg(FIN_PRE):
    """raft's configuration: its fact is the lab's `pkgGlobals` (`Base.lean`): the error variables
    pairwise distinct (`errVals`), the keys' read-only bytes, `nextObserverID`'s invariant. The
    proof is the lab's `initialize.lean` (dsverify-lab examples/hraft/proof 241f27e), its lemmas in
    `InitLemmas.lean`: each `errors.New` by `wp_New_excl`, which keeps three quarters of the new
    `errorString`'s field (`exclS`), whence the variables' values are pairwise distinct
    (`exclS_nodup`)."""
    errs = list(RAFT_ERRS)
    assert sorted(errs) == sorted(RAFT_ERR_CODES.values())
    before = {x: ['try wp_auto', f'wp_apply wp_New_excl as %x{x} ⟨#S{x}, #E{x}, X{x}⟩'] for x in errs}
    # inmem_store.go's `var _ CommitTrackingLogStore = &InmemCommitTrackingStore{}` (an allocation)
    before['ErrTransportShutdown'] = ['try wp_auto', 'wp_alloc_anon'] + before['ErrTransportShutdown']
    # progress.go's `var _ ReadCloserWrapper = &countingReadCloser{}`, then raft.go's three keys
    before['keyCurrentTerm'] = ['try wp_auto', 'wp_alloc_anon', 'try wp_auto'] + [
        l for k, b in RAFT_KEYS.items()
        for l in [f'wp_apply wp_string_to_bytes go!"{b}" as %s{k} ⟨S{k}, -⟩', 'try wp_auto']]
    before['$end'] = ['try wp_auto']
    codes = list(RAFT_ERR_CODES.items())
    finish = [f'ipersist H{x}' for x in errs] + \
        [l for k in RAFT_KEYS for l in [f'ipersist S{k}', f'ipersist H{k}']] + [
        'imod inv_alloc nextObserverIDN ⊤ (∃ n : w64, globalAddr nextObserverID ↦ n) $$ [HnextObserverID]',
        '  with #Hobs',
        '· inext; iexists _; iexact HnextObserverID',
        'let g : RaftErr → Loc := fun c =>',
        '  match c with'] + [f'    | .{c} => x{x}' for c, x in codes] + [
        'ihave %Hnd := exclS_nodup g RaftErr.all $$ [' + ' '.join(f'X{x}' for _, x in codes) + ']',
        '· simp only [RaftErr.all, g]',
        '  iframe',
        '  iapply BigSepL.bigSepL_nil.2',
        '  iempintro',
        'have Hinj : Function.Injective',
        '    (fun c => interface.mkOk (go.GoType.PointerType errors.errorString.ty) #(g c)) := by',
        '  intro a b h',
        '  have h1 : g a = g b := by',
        '    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h',
        '    exact go.intoVal_inj h.2',
        '  have hall : ∀ c, c ∈ RaftErr.all := by intro c; cases c <;> simp [RaftErr.all]',
        '  exact nodup_map_inj g Hnd (hall a) (hall b) h1'] + FIN_PRE[:6] + [
        'imodintro',
        'unfold pkgGlobals',
        'isplitr',
        '· iexists (fun c => interface.mkOk (go.GoType.PointerType errors.errorString.ty) #(g c))',
        '  unfold errVals',
        '  isplitr',
        '  · ipureintro; exact Hinj',
        '  iapply (bigSepL_all _).2',
        '  simp only [g, RaftErr.var, RaftErr.msg]',
        '  iframe #'] + [
        l for _, x in codes[:-1]
        for l in ['  isplitr', f'  · iunfold errors.newVar; iexists _; iframe H{x} S{x} E{x}']] + [
        f'  iunfold errors.newVar; iexists _; iframe H{codes[-1][1]} S{codes[-1][1]} E{codes[-1][1]}'] + [
        l for k in RAFT_KEYS for l in ['isplitr', f'· iexists s{k}; iframe #']] + ['iexact Hobs']
    return dict(
        doc='''Its fact (`pkgGlobals`, `Base.lean`, the lab's): its error variables (translated `errors.New`
calls) hold pairwise distinct errors, each `errors.newVar` of its message (`errVals`), the three
stable-store keys read-only bytes, and `nextObserverID` an invariant. Its initializer allocates its
variables, initializes its imports and runs their translated initializers; the proof is the lab's
`initialize.lean` (its lemmas: `InitLemmas.lean`).''',
        imports=['Perennial.Proof.errors.NewVar', 'Dsverify.Proof.github_com.hashicorp.raft.InitLemmas'],
        alloc_types=dict({x: 'GoInterface' for x in errs}, **{k: 'GoSlice' for k in RAFT_KEYS},
                         nextObserverID='w64'),
        before=before,
        finish=finish)


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals). raft's fact is the
    lab's `pkgGlobals` (`raft_cfg`); snapstore's is its `errors.New` variables' `errors.newVar`s,
    as craq's."""
    SPECIAL, FIN_PRE = {}, g.FIN_PRE

    def errs_cfg(xs, extra_alloc):
        return dict(
            doc=f'''Its fact (`Base.lean`): its error variables ({", ".join("`" + x + "`" for x in xs)}, translated
`errors.New` calls) each hold `errors.New` of their message (`errors.newVar`). Its initializer
allocates its variables, initializes its imports and runs their translated initializers.''',
            imports=['Perennial.Proof.errors.NewVar'],
            alloc_types=dict({x: 'GoInterface' for x in xs}, **extra_alloc),
            before=dict({x: ['try wp_auto', f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{x} ⟨#S{x}, #M{x}⟩']
                         for x in xs}, **{'$end': ['try wp_auto']}),
            finish=[f'ipersist H{x}' for x in xs] + FIN_PRE[:6] + ['imodintro',
                   'unfold _root_.Perennial.errors.newVar'] +
                   [l for x in xs[:-1] for l in ['isplitr', f'· iexists _; iframe H{x} S{x} M{x}']] +
                   [f'iexists _; iframe H{xs[-1]} S{xs[-1]} M{xs[-1]}'])

    SPECIAL[HRAFT] = raft_cfg(FIN_PRE)
    # snapstore's fact is the lab's `isInit` (its conjuncts named): unfolded before the conjuncts
    SPECIAL[f'{HRAFT}.examples.snapstore'] = errs_cfg(list(SNAP_ERRS), {})
    fin = SPECIAL[f'{HRAFT}.examples.snapstore']['finish']
    i = fin.index('unfold _root_.Perennial.errors.newVar')
    fin[i:i] = ['unfold isInit']
    # (hraft_robust R3) the disk's fact: its error variables' `errors.newVar`s
    SPECIAL[f'{HRAFT}.examples.hraftnet.disk'] = errs_cfg(list(DISK_ERRS), {})
    fin = SPECIAL[f'{HRAFT}.examples.hraftnet.disk']['finish']
    i = fin.index('unfold _root_.Perennial.errors.newVar')
    fin[i:i] = ['unfold isInit']
    SPECIAL[_DURABLE] = g.WT_SPECIAL[_DURABLE]
    return SPECIAL


# etc/dsv/kitgen.py (notes/dsv-kitgen.md): the twelve machines' commands, the kit's constants and
# addresses (`kit_gen.go`), the net/rpc codec (rpcgen, from `rpc.toml`), the addresses' Lean module
# and the statement's definitions (`TopLevelDefs.lean`). The statement itself is hand-written
# (its thread and step bounds are the proof's: `Dsverify/Spec/.../hraftnet/TopLevelRobustness.lean`);
# its proof, the commands' `wp_main`s and the boot tables come with the proofs (S5/S6).
_HRAFTNET = f'{HRAFT}.examples.hraftnet'
# the deployment's machines are examples/lib/robust's (a network namespace each, machine k at
# 10.77.k.1, in this order): servers 1..6 are machines 1..6, clients 0..4 machines 7..11, the
# orchestrator machine 12 (it listens nowhere)
_SRV = [f'10.77.{s}.1' for s in range(1, 7)]
_CLI = [f'10.77.{7 + c}.1' for c in range(5)]
KITGEN = dict(
    name='hraft',
    title='hraft',
    go_module_dir=os.path.join('examples', 'dsverify', 'hraft'),
    go_pkg_dir=os.path.join('examples', 'hraftnet'),
    go_import='github.com/hashicorp/raft/examples/hraftnet',
    go_pkg='hraftnet',
    lean_pkg=_HRAFTNET,
    proof_roots=['github_com/hashicorp'],
    prompt=dict(system='a hashicorp/raft deployment over net/rpc',
                check="whose driver changes the membership at random and runs a linearizability check of "
                      "the clients' history"),
    roles=[
        dict(cmd='orch', go_doc="the hraft kit's orchestrator machine", go_call='Orch()'),
        dict(cmd='client{id}', ids=list(range(5)), go_doc="the hraft kit's client machine {id}",
             go_call='Client({id})'),
        dict(cmd='server{id}', ids=list(range(1, 7)), go_doc="the hraft kit's server machine {id}",
             go_call='Server({id})'),
    ],
    go_consts=dict(
        consts=[
            ('NC', 'uint64', '5', 'clients'),
            ('NS', 'uint64', '6', 'servers (the first configuration holds 3 or 5 of them, as voters)'),
            ('MaxOps', 'uint64', '1 << 20', 'the most operations a client makes (Orch draws 1 to MaxOps)'),
            ('Tries', 'uint64', '30', 'the most servers an operation is tried at'),
            ('RetryMs', 'uint64', '10', 'the wait before an operation is tried at the next server, or a Listen again'),
            ('RPCTimeoutMs', 'uint64', '500', "a raft RPC's wait for its answer (upstream InmemTransport's)"),
            ('EnqueueMs', 'uint64', '100', "the timeout of the server's calls of raft that take one"),
            ('FutureMs', 'uint64', '1000', "the server's wait for a raft future"),
            ('APITimeoutMs', 'uint64', '5000', "a call's wait for a server's API answer"),
            ('AdminMs', 'uint64', '50', "the most the admin waits between two requests"),
            ('IdleMs', 'uint64', '10000', "a server's main goroutine's sleep"),
            ('AttemptMs', 'uint64', '30000', "a call between the orchestrator and a client machine"),
        ],
        addrs={
            'ServerAddrs': ("ServerAddrs is the server machines' net/rpc addresses (raft's RPCs and the "
                            "API), index id-1 server id's.", [f'{h}:7700' for h in _SRV]),
            'ConfAddrs': ("ConfAddrs is the server machines' configuration addresses (awaitConf), index "
                          "id-1 server id's.", [f'{h}:7701' for h in _SRV]),
            'ClientAddrs': ("ClientAddrs is the client machines' addresses for the orchestrator's calls "
                            "(remote.Serve), index c client c's.", [f'{h}:7700' for h in _CLI]),
        },
    ),
    codecs=[('rpc', 'examples/dsverify/hraft/examples/hraftnet/rpc.toml',
             'examples/dsverify/hraft/examples/hraftnet', 'hraftnet')],
    addrs_module=dict(
        doc='''The hraft kit's addresses: the server machines' net/rpc addresses (`ServerAddrs()`) and
configuration addresses (`ConfAddrs()`), and the client machines' (`ClientAddrs()`), the lists the
statement's `hraftKitAddrs` joins (`TopLevelDefs.lean`).''',
        defs=[(_HRAFTNET, '\n\n'.join([
            "/-- The server machines' net/rpc addresses (`ServerAddrs()`). -/\ndef serverAddrs : List GoString :=\n  ["
            + ', '.join(f'go!"{h}:7700"' for h in _SRV) + ']',
            "/-- The server machines' configuration addresses (`ConfAddrs()`). -/\ndef confAddrs : List GoString :=\n  ["
            + ', '.join(f'go!"{h}:7701"' for h in _SRV) + ']',
            "/-- The client machines' addresses (`ClientAddrs()`), for the orchestrator's calls. -/\n"
            "def clientAddrs : List GoString :=\n  [" + ', '.join(f'go!"{h}:7700"' for h in _CLI) + ']']))],
    ),
    defs=dict(
        doc='''The hraft kit's deployment (notes/dsv-hraft.md): its twelve machines' boot programs and addresses, the
definitions its top-level statement (`Spec/.../hraftnet/TopLevelRobustness.lean`) names.''',
        imports=[f'public import Dsverify.Proof.{HRAFT}.examples.hraftnet.Addrs',
                 'public import Net.Statement.DistDeploy', 'public import Robustness.Statement'],
        system_doc='''The system: the twelve machines, from the local states `σ i`: the orchestrator, client machines
0..4, server machines 1..6 (each a command of `examples/hraftnet/cmd`).''',
        addrs_def='''/-- The deployment's addresses: the server machines' net/rpc and configuration addresses, the client
machines' (`ServerAddrs()`, `ConfAddrs()`, `ClientAddrs()`). -/
def hraftKitAddrs : List GoString := serverAddrs ++ confAddrs ++ clientAddrs

/-- The step bound: the proof's (dsverify-lab hraft-4's receipt bound, `ReceiptBoundLe (2 ^ 62)`:
terms and indexes stay below `2 ^ 62`). -/
def hraftStepBound : Nat := 2 ^ 62

/-- The thread bound: the proof's (dsverify-lab hraft-4's D15: `goFunc`'s `WaitGroup` and the
`RWMutex` reader pools split into quarter thread tokens); below net/rpc's server's `2 ^ 31` and
net/http's first initialization's `2 ^ 30`. -/
def hraftThreadBound : Nat := 2 ^ 28''',
    ),
    boot=dict(
        # the table: server1's chain (etc/gen-init.py's cmd/server1/PkgTable.lean); every command's
        # chain is the same but its own package
        table='server1',
        owned=[_HRAFTNET, 'net.rpc'],
        table_doc='''The package facts of the hraft kit's boot (notes/dsv-hraft.md, "The boot"): generic in a program's
table `G` that gives every package of `hraftnet`'s import closure its `isPkgInit` (`KitG G`), the
facts at `G` (`wf_*`) and, for the packages whose closure avoids the kit's owned packages
(`ownedPkgs`: `hraftnet`, whose first initialization the boot proves, and net/rpc's, Net's first run),
at `gOff S G` for `S` a sub-list of `ownedPkgs` (`wfO_*`): the table in which the packages of `S` are
not initialized yet.''',
        cmds_doc='''The hraft kit's twelve commands' boots (notes/dsv-hraft.md, "The boot"): each command's
initialization from the machine's empty package state, its first, through `hraftnet`'s
(`BootLinked.lean`, `boot_hraftnet`), at the command's table (`getIsPkgInit`, its `PkgTable.lean`;
`kitG`).''',
        opens=['open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net',
               f'open {HRAFT} {_HRAFTNET}',
               'open EtcdGrove (wp_package_init_first)'],
        attributes=['attribute [local instance] GooseGlobalGS.gooseInvGS'],
        variables='''variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : cmd.{n}.Assumptions] [π : NetProtoGS]''',
        returns="returns net/rpc's codec unregistered (`codecUnset`, net/rpc's first run's).",
        q='net.rpc.codecUnset',
        post='        isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗ net.rpc.codecUnset',
    ),
    # hraft_robust: the restartable server machines' commands `cmd/rserver1..6` (package `rserver`),
    # their table rserver1's chain, in `rserver`'s namespace; the boot lemma `rserver.boot_rserver`
    # (`RBootLinked.lean`): `rserver`'s first initialization, through `rpctransport`'s, net/rpc's first
    # run (the packages whose first run is proved there: `rserver`, `rpctransport`, net/rpc)
    boots=[dict(
        table='rserver1',
        table_pkg=f'{_HRAFTNET}.rserver',
        table_ns='rserver.',
        cmds=[f'rserver{s}' for s in range(1, 7)],
        cmds_file='RBootCmdsLinked.lean',
        boot='rserver.boot_rserver',
        boot_import=f'Dsverify.Proof.{_HRAFTNET}.RBootLinked',
        owned=[f'{_HRAFTNET}.rserver', f'{_HRAFTNET}.rpctransport', 'net.rpc'],
        table_doc='''The package facts of the hraft kit's restartable servers' boot (hraft_robust; notes/dsv-hraft.md, "The
boot"): generic in a program's table `G` that gives every package of `rserver`'s import closure its
`isPkgInit` (`KitG G`), the facts at `G` (`wf_*`) and, for the packages whose closure avoids the owned
packages (`ownedPkgs`: `rserver` and `rpctransport`, whose first initializations the boot proves, and
net/rpc's, Net's first run), at `gOff S G` for `S` a sub-list of `ownedPkgs` (`wfO_*`): the table in which
the packages of `S` are not initialized yet.''',
        cmds_doc='''The hraft kit's restartable server commands' boots (hraft_robust; notes/dsv-hraft.md, "The boot"):
each command's initialization from the machine's empty package state, its first, through `rserver`'s
(`RBootLinked.lean`, `rserver.boot_rserver`), at the command's table (`getIsPkgInit`, its
`PkgTable.lean`; `kitG`).''',
        opens=['open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net',
               f'open {HRAFT} {_HRAFTNET}',
               'open EtcdGrove (wp_package_init_first)'],
        attributes=['attribute [local instance] GooseGlobalGS.gooseInvGS'],
        variables='''variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : cmd.{n}.Assumptions] [π : NetProtoGS]''',
        returns="returns net/rpc's codec unregistered (`codecUnset`, net/rpc's first run's), as the servers'.",
        q='net.rpc.codecUnset',
        post='        isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗ net.rpc.codecUnset',
    )],
)
