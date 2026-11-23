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
                "encoding/json=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall="],
    packages=["./pkg/assert", "./pkg/log", "./pkg/ipv4port", "./pkg/events", "./pkg/queue",
              "./pkg/time", "./pkg/network", "./pkg/client", "./pkg/replica",
              "./examples/vsrwire", "./examples/vsrkv", "./examples/vsrnet",
              "./examples/vsrnet/cmd/orch", "log/slog"]
             + ["./examples/vsrnet/cmd/client%d" % c for c in range(6)]
             + ["./examples/vsrnet/cmd/server%d" % s for s in range(1, 6)],
    owned=[os.path.join("github_com", "tangledbytes"), os.path.join("log", "slog")],
    std_models=["encoding/json", "log/slog"],
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
