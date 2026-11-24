"""The vr kit (notes/dsv-vr.md): its etc/goose.py project and etc/gen-init.py configuration
(format: etc/dsv/README.md)."""
import os

# etc/goose.py's project dsv-vr (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-vr",
    # dsverify-lab's vr kit (notes/dsv-vr.md; notes/dsverify-net-port-plan.md, phase 6): the
    # lab's vsr-bump-1 fork of tangledbytes/go-vsr (examples/vr/fork/go-vsr at lab master
    # 915f964) with its kit ported onto examples/lib/remote, `examples/dsverify/vr` (a Go module
    # of its own, module path the fork's). Into the part `Dsverify/`, with remote and `net` the
    # part `Net/`'s, lintest, porcupine and `encoding/json` (the model, `models/encoding/json`: the
    # main tree's, J1/J2 of mit-pdos/etcd-grove#24) the main tree's; `log/slog` (the model, with its
    # bodies) into the part (`Dsverify/Code/log/slog.toml`).
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "vr"),
    root="Dsverify",
    lean_roots=["github.com/tangledbytes/go-vsr=Dsverify", "log/slog=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "encoding/json=", "models.lab=Net",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall="],
    packages=["./pkg/assert", "./pkg/log", "./pkg/ipv4port", "./pkg/events", "./pkg/queue",
              "./pkg/time", "./pkg/network", "./pkg/client", "./pkg/replica",
              "./examples/vsrwire", "./examples/vsrkv", "./examples/vsrnet",
              "./examples/vsrnet/cmd/orch", "log/slog"]
             + ["./examples/vsrnet/cmd/client%d" % c for c in range(6)]
             + ["./examples/vsrnet/cmd/server%d" % s for s in range(1, 6)],
    owned=[os.path.join("github_com", "tangledbytes"), os.path.join("log", "slog")],
    std_models=["encoding/json", "log/slog"],
    # (#24 J3) the kit's named JSON types get jsongen's same-package methods (`JSONModel*`,
    # `json_model_gen.go` in their packages, by goose's overlay: etc/goose.py `jsonmodel_roots`):
    # every message type `events.Event` carries, the event itself, vsrwire's frame and go-vsr's
    # `log.Logs` (whose own MarshalJSON/UnmarshalJSON the methods call). The unnamed roots
    # (`[]log.Log`, the unnamed frame) are the registered codec's (`examples/vsrnet/json.toml`).
    jsonmodel_roots=["github.com/tangledbytes/go-vsr/pkg/events." + t
                     for t in ("Event", "Request", "Reply", "Prepare", "PrepareOK", "Commit",
                               "StartViewChange", "DoViewChange", "StartView", "GetState",
                               "NewState", "Heartbeat")]
                    + ["github.com/tangledbytes/go-vsr/examples/vsrwire.Frame",
                       "github.com/tangledbytes/go-vsr/pkg/log.Logs"],
)

# etc/gen-init.py: go-vsr's packages, the kit and its twelve machines' commands, and `log/slog`
# (the model). `encoding/json` is the main tree's (`MAIN`); its `wp_initialize'` is proved (J1,
# mit-pdos/etcd-grove#24), its `Init.lean` generated into the part (`MAIN_GEN`), as epaxos's.
VR = 'github_com.tangledbytes.go_vsr'
NODES = ['orch'] + [f'client{c}' for c in range(6)] + [f'server{s}' for s in range(1, 6)]
PKGS = [f'{VR}.pkg.{p}' for p in ['assert', 'log', 'ipv4port', 'events', 'queue', 'time',
                                  'network', 'client', 'replica']] + \
    [f'{VR}.examples.{p}' for p in ['vsrwire', 'vsrkv', 'vsrnet']] + \
    [f'{VR}.examples.vsrnet.cmd.{n}' for n in NODES] + ['log.slog']
PROGRAMS = {f'{VR}.examples.vsrnet.cmd.{n}':
            f'Proof/{VR.replace(".", "/")}/examples/vsrnet/cmd/{n}/PkgTable.lean' for n in NODES}
# the main tree's packages the part's closure adds to `NET_MAIN`
MAIN = ['encoding.json']
MAIN_GEN = ['encoding.json']
HYP_INITS = []


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL, newvars_cfg, FIN_PRE, DSV_VR = {}, g.newvars_cfg, g.FIN_PRE, VR
    # their package variables: `events`' error, mutex and frame decoder (`nil` until `vsrwire`'s `init`
    # sets it) and `network`'s error (translated `errors.New` calls; the facts are `True` for now)
    SPECIAL[f'{DSV_VR}.pkg.events'] = newvars_cfg(dict(
        doc='''Its fact (`hookKnownFull`, `Base.lean`): the frame-decoder hook's lock, with its flag.
Its initializer allocates its variables (`ErrInvalidEventType`, an `errors.New` call;
`frameDecoderMu`, a new mutex guarding `frameDecoder`, `nil`, and the flag, unset) and
initializes its imports.''',
        imports=['Perennial.Ghost.MonoList'],
        alloc_types={'frameDecoderMu': 'Loc', 'frameDecoder': 'GoFunc'},
        finish=['imod (mono_list_own_alloc (GF := GF) ([] : List Unit)) with ⟨%γh, Ha, -⟩',
                'imod _root_.Perennial.sync.init_Mutex (hookLockInvFull (GF := GF) γh) ⊤ _ $$ «$r0» [HframeDecoder Ha] with #Hmu',
                '· inext; iunfold hookLockInvFull; iexists _; iframe HframeDecoder; ileft; iframe Ha; ipureintro; rfl',
                'imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HframeDecoderMu with #HframeDecoderMu'] +
               FIN_PRE[:6] + ['imodintro', 'iunfold hookKnownFull', 'iexists γh', 'iunfold hookState',
                              'iexists _', 'iframe HframeDecoderMu', 'iexact Hmu']),
        ['ErrInvalidEventType'])
    SPECIAL[f'{DSV_VR}.examples.vsrwire'] = dict(
        doc='''Its fact (`events.frameDecoderSet`, `Base.lean`): the hook set for good. Its
initializer initializes its imports and runs its `init()`, which sets `events`' frame-decoder hook
to `decodeFrame` (`events.wp_SetFrameDecoder`).''',
        imports=[f'Dsverify.Proof.{DSV_VR}.pkg.events.SetFrameDecoder'],
        after={'init.«0»': [f'wp_apply _root_.Perennial.{DSV_VR}.pkg.events.wp_SetFrameDecoder as #Hset',
                            'try wp_auto']},
        finish=FIN_PRE[:6],
    )
    net_msg = 'network: no connection to the source address'
    SPECIAL[f'{DSV_VR}.pkg.network'] = newvars_cfg(dict(
        doc='''Its fact (`Base.lean`): `ErrNoConn` holds `errors.New(...)` for good (`errors.newVar`).
Its initializer allocates `ErrNoConn` (an `errors.New` call) and initializes its imports.''',
        finish=['try wp_auto', 'ipersist HErrNoConn'] + FIN_PRE[:6] +
               ['imodintro', 'iunfold _root_.Perennial.errors.newVar', 'iexists xErrNoConn',
                'iframe HErrNoConn SErrNoConn MErrNoConn']), ['ErrNoConn'])
    SPECIAL[f'{DSV_VR}.pkg.network']['before']['ErrNoConn'] = [
        'try wp_auto',
        'wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrNoConn ⟨#SErrNoConn, #MErrNoConn⟩']

    # log/slog (the model, translated with its bodies): its two variables, `DiscardHandler`
    # (`discardHandler{}` as a `Handler`) and `defaultLogger` (a new `Logger` over `defaultHandler{}`)
    SPECIAL['log.slog'] = dict(
        doc='''Its fact (`pkgState`, `Base.lean`): `DiscardHandler` holds `dhV` and `defaultLogger`
points to a `Logger` whose handler is `defHV`, both read-only for good. Its initializer allocates
the two variables, initializes its imports and runs their translated initializers (a conversion to
`Handler`; a new `Logger`).''',
        alloc_types={'DiscardHandler': 'GoInterface', 'defaultLogger': 'Loc'},
        finish=['try wp_auto', 'ipersist HDiscardHandler', 'ipersist HdefaultLogger',
                'iStructNamed «$r0»', 'ipersist handler'] + FIN_PRE[:6] +
               ['imodintro', 'iunfold _root_.Perennial.log.slog.pkgState', 'iframe HDiscardHandler',
                'iexists _', 'iframe HdefaultLogger handler'],
    )
    return SPECIAL


# etc/dsv/kitgen.py (notes/dsv-kitgen.md): the first-run boot's tables, `BootTable.lean` and
# `BootCmdsLinked.lean` (formerly etc/dsv/_vr_boot.py's; notes/dsv-vr.md, "Round 7", the boot). The
# owned packages are the path of encoding/json's first run on a machine: `vsrnet` runs `replica`'s
# first, `replica` `network`'s, `network` encoding/json's. The machines are listed for their order
# only (the commands' mains stay as they are).
KITGEN = dict(
    name='vr',
    go_mains=False,
    lean_pkg=f'{VR}.examples.vsrnet',
    proof_roots=[VR],  # the kit's own Lean trees (kitgen --export-challenge)
    # the encoding/json model's registered codec (models/json/jsongen.py; vsrnet/json.toml)
    codecs=[('json', 'examples/dsverify/vr/examples/vsrnet/json.toml',
             'examples/dsverify/vr/examples/vsrnet', 'vsrnet')],
    roles=[dict(cmd='orch'), dict(cmd='client{id}', ids=list(range(6))),
           dict(cmd='server{id}', ids=list(range(1, 6)))],
    boot=dict(
        # the table: server1's chain (etc/gen-init.py's cmd/server1/PkgTable.lean)
        table='server1',
        owned=[f'{VR}.examples.vsrnet', f'{VR}.pkg.replica', f'{VR}.pkg.network', 'encoding.json'],
        table_doc='''The package facts of the vr kit's boot (notes/dsv-vr.md, "Round 7", the boot; as
swiftpaxos's): generic in a program's table `G` that gives every package of `vsrnet`'s import
closure its `isPkgInit` (`KitG G`), the facts at `G` (`wf_*`) and, for the packages whose closure
avoids the kit's owned packages (`ownedPkgs`: the path of encoding/json's first run, whose first
initializations the boot proves), at `gOff S G` for `S` a sub-list of `ownedPkgs` (`wfO_*`): the
table in which the packages of `S` are not initialized yet.''',
        cmds_doc='''The vr kit's twelve commands' boots (notes/dsv-vr.md, "Round 7", the boot): each command's
initialization from the machine's empty package state, its first, through `vsrnet`'s
(`BootLinked.lean`, `boot_vsrnet`), at the command's table (`getIsPkgInit`, its `PkgTable.lean`;
`kitG`), returning encoding/json's fresh registry (`codecFresh`).''',
        opens=['open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode',
               f'open {VR} {VR}.examples.vsrnet',
               'open github_com.imdea_software.swiftpaxos (wp_package_init_first)'],
        variables='''variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : cmd.{n}.Assumptions]''',
        returns="returns encoding/json's fresh registry (`codecFresh`).",
        q='encoding.json.codecFresh (GF := GF)',
        q_sep='\n    ',
        post='''        isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗
        encoding.json.codecFresh (GF := GF)''',
    ),
)
