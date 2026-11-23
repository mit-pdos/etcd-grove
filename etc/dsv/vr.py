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
    # part `Net/`'s, lintest and porcupine the main tree's; `encoding/json` (the model,
    # `models/encoding/json`) and `log/slog` names-only into the part (`Dsverify/Code/{encoding/json,log/slog}.toml`):
    # their specs are the proof's hypotheses until their models' Lean halves exist.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "vr"),
    root="Dsverify",
    lean_roots=["github.com/tangledbytes/go-vsr=Dsverify", "log/slog=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "encoding/json=Dsverify",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall="],
    packages=["./pkg/assert", "./pkg/log", "./pkg/ipv4port", "./pkg/events", "./pkg/queue",
              "./pkg/time", "./pkg/network", "./pkg/client", "./pkg/replica",
              "./examples/vsrwire", "./examples/vsrkv", "./examples/vsrnet",
              "./examples/vsrnet/cmd/orch", "log/slog", "encoding/json"]
             + ["./examples/vsrnet/cmd/client%d" % c for c in range(6)]
             + ["./examples/vsrnet/cmd/server%d" % s for s in range(1, 6)],
    owned=[os.path.join("github_com", "tangledbytes"), os.path.join("log", "slog"),
           os.path.join("encoding", "json")],
    std_models=["encoding/json"],
)

# etc/gen-init.py: go-vsr's packages, the kit and its twelve machines' commands. The names-only
# `encoding.json` (the model) and `log.slog` are external here: their `wp_initialize'` is a
# hypothesis (`Dsverify/Proof/<pkg>/Init.lean`'s class `InitHyp`), which every generated theorem
# initializing them takes as an instance (`HYP_INITS`: a section variable added to the files that
# name it).
VR = 'github_com.tangledbytes.go_vsr'
NODES = ['orch'] + [f'client{c}' for c in range(6)] + [f'server{s}' for s in range(1, 6)]
PKGS = [f'{VR}.pkg.{p}' for p in ['assert', 'log', 'ipv4port', 'events', 'queue', 'time',
                                  'network', 'client', 'replica']] + \
    [f'{VR}.examples.{p}' for p in ['vsrwire', 'vsrkv', 'vsrnet']] + \
    [f'{VR}.examples.vsrnet.cmd.{n}' for n in NODES]
PROGRAMS = {f'{VR}.examples.vsrnet.cmd.{n}':
            f'Proof/{VR.replace(".", "/")}/examples/vsrnet/cmd/{n}/PkgTable.lean' for n in NODES}
HYP_INITS = ['encoding.json', 'log.slog']


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL, newvars_cfg, FIN_PRE, DSV_VR = {}, g.newvars_cfg, g.FIN_PRE, VR
    # their package variables: `events`' error, mutex and frame decoder (`nil` until `vsrwire`'s `init`
    # sets it) and `network`'s error (translated `errors.New` calls; the facts are `True` for now)
    SPECIAL[f'{DSV_VR}.pkg.events'] = newvars_cfg(dict(
        doc='''Its fact (`hookKnown`, `Base.lean`): the frame-decoder hook's lock. Its initializer
allocates its variables (`ErrInvalidEventType`, an `errors.New` call; `frameDecoderMu`, a new mutex
guarding `frameDecoder`, `nil`) and initializes its imports.''',
        alloc_types={'frameDecoderMu': 'Loc', 'frameDecoder': 'GoFunc'},
        finish=['imod _root_.Perennial.sync.init_Mutex (hookLockInv (GF := GF)) ⊤ _ $$ «$r0» [HframeDecoder] with #Hmu',
                '· inext; iunfold hookLockInv; iexists _; iexact HframeDecoder',
                'imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HframeDecoderMu with #HframeDecoderMu'] +
               FIN_PRE[:6] + ['imodintro', 'iunfold hookKnown', 'iexists _', 'iframe HframeDecoderMu', 'iexact Hmu']),
        ['ErrInvalidEventType'])
    SPECIAL[f'{DSV_VR}.examples.vsrwire'] = dict(
        doc='''Its fact is `True` (for now; the lab's is `frameDecoderSet`, the hook set for good). Its
initializer initializes its imports and runs its `init()`, which sets `events`' frame-decoder hook
(`events.wp_SetFrameDecoder`).''',
        imports=[f'Dsverify.Proof.{DSV_VR}.pkg.events.SetFrameDecoder'],
        after={'init.«0»': [f'wp_apply _root_.Perennial.{DSV_VR}.pkg.events.wp_SetFrameDecoder', 'try wp_auto']},
    )
    SPECIAL[f'{DSV_VR}.pkg.network'] = newvars_cfg(dict(
        doc='''Its fact is `True` (for now). Its initializer allocates `ErrNoConn` (an `errors.New` call)
and initializes its imports.'''), ['ErrNoConn'])

    return SPECIAL
