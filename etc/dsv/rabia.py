"""The rabia kit (notes/dsv-rabia.md): its etc/goose.py project and etc/gen-init.py
configuration (format: etc/dsv/README.md)."""
import os

# etc/goose.py's project dsv-rabia (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-rabia",
    # dsverify-lab's rabia kit (notes/dsv-rabia.md; notes/dsverify-net-port-plan.md, phase 6):
    # the lab's Rabia fork (examples/rabia/fork/rabia at lab master 915f964, fork ef2a93b, run
    # rabia-r1wake-1) with its kit ported onto examples/lib/remote, `examples/dsverify/rabia`
    # (module `rabia`). Into the part `Dsverify/`, with remote and `net` the part `Net/`'s,
    # lintest, porcupine, bufio, container/heap and path the main tree's; zerolog, gogo/protobuf,
    # go-redis and os/signal names only into the part (no model here: notes/dsv-rabia.md).
    # go-redis is v8.11.5 (the fork pins v8.8.2), the version the QuePaxa kit builds with: this
    # project owns the one go-redis translation in `Dsverify/`, which both kits' theorems use
    # (issue #24).
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "rabia"),
    root="Dsverify",
    expand_comment_tabs=True,
    lean_roots=["rabia=Dsverify", "github.com/rs/zerolog=Dsverify",
                "github.com/gogo/protobuf=Dsverify", "github.com/go-redis/redis/v8=Dsverify",
                "os/signal=Dsverify", "io/ioutil=Dsverify",
                "encoding/json=", "path/filepath=", "internal/filepathlite=",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall=",
                "bufio=", "container/heap=", "path="],
    packages=["github.com/rs/zerolog", "github.com/rs/zerolog/internal/json", "github.com/gogo/protobuf/proto",
              "github.com/gogo/protobuf/gogoproto", "github.com/go-redis/redis/v8",
              "github.com/go-redis/redis/v8/internal/proto", "os/signal", "./internal/config", "./internal/message", "./internal/queue", "./internal/ledger",
              "./internal/tcp", "./internal/logger", "./internal/system",
              "./roles/server/layers/network", "./roles/server/layers/consensus",
              "./roles/server/layers/proxy", "./roles/server", "./examples/rabianet",
              "./examples/rabianet/cmd/orch"]
             + ["./examples/rabianet/cmd/client%d" % c for c in range(6)]
             + ["./examples/rabianet/cmd/server%d" % s for s in range(1, 6)],
    # (dsv-retire-3) zerolog's `InterfaceMarshalFunc = json.Marshal`: encoding/json the model's names
    std_models=["encoding/json"],
    owned=["rabia", os.path.join("github_com", "rs"), os.path.join("github_com", "gogo"),
           os.path.join("github_com", "go_redis"), os.path.join("os", "signal")],
)

# etc/gen-init.py: Rabia's packages, the names-only libraries the lab modelled, the kit and its
# programs
RABIA_NODES = ['orch'] + [f'client{c}' for c in range(6)] + [f'server{s}' for s in range(1, 6)]
PKGS = ['os.signal'] + [f'rabia.{p}' for p in ['internal.config', 'internal.message', 'internal.queue',
                               'internal.ledger', 'internal.tcp', 'internal.logger', 'internal.system',
                               'roles.server.layers.network', 'roles.server.layers.consensus',
                               'roles.server.layers.proxy', 'roles.server', 'examples.rabianet']] + \
    ['github_com.rs.zerolog.internal.json', 'github_com.rs.zerolog'] + \
    [f'rabia.examples.rabianet.cmd.{n}' for n in RABIA_NODES]
PROGRAMS = {f'rabia.examples.rabianet.cmd.{n}':
            f'Proof/rabia/examples/rabianet/cmd/{n}/PkgTable.lean' for n in RABIA_NODES}
# the main tree's packages the kit imports beside `NET_MAIN`'s (bufio, container/heap, path)
# (their `Init.lean` the main tree's, etc/gen-init.py's `shared_inits`, as `Net/`'s `NET_MAIN`'s; the
# instances of `container.heap` and `path` the main tree's `Proof/<pkg>/PkgInit.lean` (L1,
# 2026-11-24); `internal.bytealg` is Perennial's)
MAIN = ['bufio', 'container.heap', 'path', 'path.filepath', 'internal.filepathlite', 'encoding.json']
# the names-only libraries are external here, as dsv-vr's: their `wp_initialize'` is a
# trust-boundary axiom (`Dsverify/Proof/<pkg>/Init.lean`; dsv-fix3, #8 2026-11-25T02:20:53Z: until
# then the class `InitHyp`, a premise of the statement), but go-redis's, still `InitHyp` and a
# premise (gen-init's `DSV_PREMISE_INITS`: its axiom review refuted it). Not math/rand (math-rand-isinit, 2026-11-24): Perennial proves its
# `wp_initialize'` (`Perennial.Proof.math.rand.Link`), external like Perennial's other packages, so
# neither here nor in `MAIN`
HYP_INITS = ['github_com.gogo.protobuf.proto',
             'github_com.gogo.protobuf.gogoproto', 'github_com.go_redis.redis.v8',
             'github_com.go_redis.redis.v8.internal.proto']
# Not zerolog nor its `internal/json` (dsv-retire-3, 2026-11-26): translated with bodies, their
# `Init.lean` generated (`PKGS`) with a proved `wp_initialize'`.
# Not os/signal (dsv-retire-1-inits, 2026-11-25): its variables and `init` are translated, its
# `Init.lean` generated (`PKGS`) with a proved `wp_initialize'`


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL, newvars_cfg, FIN_PRE = {}, g.newvars_cfg, g.FIN_PRE
    # (dsv-retire-1-inits) os/signal: the zero-valued `handlers`, `watchSignalLoopOnce`,
    # `watchSignalLoop`, and `init.0` (`watchSignalLoop = loop`)
    SPECIAL['os.signal'] = dict(
        doc='''Its fact is `True`. Its initializer allocates `handlers`, `watchSignalLoopOnce` and
`watchSignalLoop` (zero values), initializes its imports `os` and `sync`, and runs its `init`, which
stores the function value `loop` (not called) in `watchSignalLoop`.''',
        alloc_types={'handlers': '_root_.Perennial.os.signal.«struct#c69a5a71»',
                     'watchSignalLoopOnce': '_root_.Perennial.sync.Once',
                     'watchSignalLoop': 'GoFunc'})
    SPECIAL['rabia.internal.config'] = dict(
        doc='''Its fact (`Base.lean`): `Conf`'s invariant `confInv`, as initialized. Its initializer
allocates `Conf` and initializes its imports.''',
        alloc_types={'Conf': 'rabia.internal.config.Config'},
        finish=['imod (inv_alloc _root_.Perennial.rabia.internal.config.confN ⊤ '
                '(_root_.Perennial.rabia.internal.config.confInv (GF := GF))) $$ [HConf] with #Hcinv',
                '· inext; iunfold _root_.Perennial.rabia.internal.config.confInv; ileft; iexact HConf'] +
               FIN_PRE[:6])
    # rabia's `message` (message.pb.go's variables and two `init`s): the errors (`errors.New`, verb-less
    # `fmt.Errorf`), the `MsgType` maps, the file descriptor's slice, and gogo proto's `Register*` calls,
    # whose specs are the fields of the hypothesis `proto.Hyps` (names only here: notes/dsv-rabia.md),
    # carried by every package above (`vars`)
    _DSV_MSG = 'rabia.internal.message'
    _DSV_IMI = '_root_.Perennial.github_com.gogo.protobuf.proto.InternalMessageInfo'
    _DSV_PH = '_root_.Perennial.github_com.gogo.protobuf.proto.Hyps'
    SPECIAL[_DSV_MSG] = newvars_cfg({
        'alloc_types': {'MsgType_name': 'Loc', 'MsgType_value': 'Loc',
                        'fileDescriptor_33c57e4bae7b9afd': 'GoSlice', 'xxx_messageInfo_Msg': _DSV_IMI,
                        'xxx_messageInfo_ConsensusObj': _DSV_IMI, 'xxx_messageInfo_Command': _DSV_IMI},
        'before': {
            'MsgType_name': ['try wp_auto',
                             'wp_apply (wp_map_make1 (K := w32) (V := GoString)) as %mName Hm',
                             'repeat (wp_apply wp_mapInsert $$ Hm as Hm)'],
            'MsgType_value': ['try wp_auto',
                              'wp_apply (wp_map_make1 (K := GoString) (V := w32)) as %mVal Hm2',
                              'repeat (wp_apply wp_mapInsert $$ Hm2 as Hm2)'],
            'fileDescriptor_33c57e4bae7b9afd': [
                'try wp_auto', 'wp_apply wp_slice_literal (V := w8) _', 'isplitr',
                '· ipureintro; first | rfl | (with_unfolding_all rfl) | simp | decide',
                'iintro %fdp ⟨Hfds, _⟩'],
        },
        'after': {
            # (#24) the package state out of `Hown` for the `Register*` calls (`proto.Hyps`; each
            # `RegisterType` on a typed `nil` pointer, not the `nil` interface, dsv-fix3), and
            # `MsgType_value`'s points-to for `RegisterEnum` (consumed: called once, here)
            'init.«0»': ['iunfold EtcdGrove.ownInitLb at Hown',
                         'icases Hown with ⟨%σg, Hg, #Hok, %Hle⟩',
                         f'wp_apply ({_DSV_PH}.RegisterEnum (GF := GF)) $$ [$Hg $HMsgType_value] as Hg',
                         'try wp_auto',
                         f'wp_apply ({_DSV_PH}.RegisterType (GF := GF)) $$ [$Hg] as Hg',
                         '· ipureintro; first | exact nofun | simp',
                         'try wp_auto',
                         f'wp_apply ({_DSV_PH}.RegisterType (GF := GF)) $$ [$Hg] as Hg',
                         '· ipureintro; first | exact nofun | simp',
                         'try wp_auto',
                         f'wp_apply ({_DSV_PH}.RegisterType (GF := GF)) $$ [$Hg] as Hg',
                         '· ipureintro; first | exact nofun | simp',
                         'try wp_auto'],
            'init.«1»': [f'wp_apply ({_DSV_PH}.RegisterFile (GF := GF)) $$ [$Hg] as Hg',
                         'try wp_auto',
                         'ihave Hown : EtcdGrove.ownInitLb get_is_pkg_init σ0 $$ [Hg]',
                         '· iunfold EtcdGrove.ownInitLb; iexists σg; iframe Hg Hok; ipureintro; exact Hle'],
        },
        # (#24) gogo proto's `Register*` specs (`proto/Spec.lean`), a premise of their own
        'imports': ['Dsverify.Proof.github_com.gogo.protobuf.proto.Spec'],
        'vars': [f'[{_DSV_PH} GF]'],
        'rec_depth': 100000,
        'heavy': True,
        # its fact (`message/Base.lean`'s `msgFact`): the framing's two errors, non-`nil`
        'finish': ['ipersist HerrFrameTooLarge', 'ipersist HerrFrameTooLong'] + FIN_PRE[:6] +
                  ['iunfold _root_.Perennial.rabia.internal.message.msgFact',
                   'iexists _, _', 'iframe HerrFrameTooLarge HerrFrameTooLong',
                   'ipureintro', 'simp [interface.mkOk]'],
    }, ['errFrameTooLong', 'errFrameTooLarge', 'ErrInvalidLengthMessage', 'ErrIntOverflowMessage',
        'ErrUnexpectedEndOfGroupMessage'],
       errorf={'ErrInvalidLengthMessage': 'proto: negative length found during unmarshaling',
               'ErrIntOverflowMessage': 'proto: integer overflow',
               'ErrUnexpectedEndOfGroupMessage': 'proto: unexpected end of group'})

    # (dsv-retire-3, 2026-11-26) zerolog's `internal/json`: `JSONMarshalFunc` (no initializer, so
    # `nil`; zerolog's `init` sets it) and `noEscapeTable` (a zero `[256]bool`, then `init.0`'s loop)
    ZJ, ZL = 'github_com.rs.zerolog.internal.json', 'github_com.rs.zerolog'
    SPECIAL[ZJ] = dict(
        doc='''Its fact (`jsonInit`, `Base.lean`): the invariant of its hook cell `JSONMarshalFunc`
(`hookCell`, `Proof/runtime/InitInv.lean`), which zerolog's initializer, holding its package state, opens
for a plain store, and `noEscapeTable`, read-only for good. Its initializer allocates both (no
initializer for `JSONMarshalFunc`, so `nil`; a zero array for the table), initializes its imports and
runs its translated `init`, whose loop fills the table (`wp_init0`, `InitLoop.lean`). (dsv-retire-3,
2026-11-26: until then names only, zerolog's `wp_initialize'` a trust-boundary axiom.)''',
        alloc_types={'JSONMarshalFunc': 'GoFunc', 'noEscapeTable': 'GoArray Bool 256'},
        initfn_apply={'init.«0»': ['wp_apply (wp_init0 _) $$ HnoEscapeTable as ⟨%tb, HnoEscapeTable⟩',
                                  'try wp_auto']},
        imports=['Dsverify.Proof.github_com.rs.zerolog.internal.json.InitLoop'],
        finish=['imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoFunc) ⊤ _ _) '
                '$$ HJSONMarshalFunc with #CJSONMarshalFunc', 'ipersist HnoEscapeTable']
        + g.FIN_PRE[:6] + ['try imodintro', f'unfold _root_.Perennial.{ZJ}.jsonInit',
                           'iframe CJSONMarshalFunc', 'iexists _', 'iexact HnoEscapeTable'],
    )
    # (dsv-retire-3) zerolog's fact (`zerologInit`, `Base.lean`): `gLevel`'s cell into its invariant,
    # `eventPool` into a `sync.Pool` of events, the variables the fact keeps read-only (made at the end of
    # `init.0`, while the goal is still a WP), and the fact itself after `is_pkg_init_finish`
    ZL_FACT = ['-- the fact (`zerologInit`, `Base.lean`)', 'imod inv_alloc _root_.Perennial.github_com.rs.zerolog.gLevelN ⊤ (iprop(∃ v : w32, pgl ↦ v)) $$ [HgCell] with #IgCell', '· inext; iexists _; iexact HgCell', 'imod sync.init_Pool pep _ iprop(True) _root_.Perennial.github_com.rs.zerolog.eventElem ⊤ ?_ $$ [HepCell] with #Hpool', 'rotate_left', '· iframe HepCell', '  iapply sync.newSpec_of_true', '  iright', '  wp_start', '  dsimp only', '  wp_auto', '  wp_apply (wp_slice_make3 (V := w8) (W64 0) (W64 500) (by decide)) as %sb ⟨Hsb, Hcap, -⟩', '  wp_alloc le as Hle', '  wp_auto', '  iapply HΦ', '  unfold _root_.Perennial.github_com.rs.zerolog.eventElem', '  iexists le, _, _', '  iframe Hle', '  isplitr', '  · ipureintro; rfl', '  iframe', 'ipersist HgLevel', 'ipersist HLevelFieldName', 'ipersist HLevelTraceValue', 'ipersist HLevelDebugValue', 'ipersist HLevelInfoValue', 'ipersist HLevelWarnValue', 'ipersist HLevelErrorValue', 'ipersist HLevelFieldMarshalFunc', 'ipersist Henc', 'ipersist HeventPool']
    ZL_FIN = ['try imodintro', 'unfold _root_.Perennial.github_com.rs.zerolog.zerologInit', 'isplitl []', '· iexists pgl; iframe #', 'isplitl []', '· iexact HLevelFieldName', 'isplitl []', '· iexists _; iframe HLevelFieldMarshalFunc', '  unfold _root_.Perennial.github_com.rs.zerolog.marshalSpec', '  iintro %lv', '  wp_start as %hlv', '  haveI : go.NotInterface go.int8 := ⟨by simp [go.int8]⟩', '  simp only [_root_.Perennial.github_com.rs.zerolog.fiveLevels, List.mem_cons, List.not_mem_nil,', '    _root_.or_false] at hlv', '  rcases hlv with rfl | rfl | rfl | rfl | rfl', '  all_goals (repeat (first | wp_method_call | wp_call | wp_auto))', '  all_goals (simp (config := { decide := true }) only', '    [_root_.Perennial.github_com.rs.zerolog.levelString, ↓reduceIte]; iapply HΦ; itrivial)', 'isplitl []', '· iexact Henc', 'isplitl []', '· iexists pep, _; iframe #; ipureintro; simp [func.nil]', 'iexists wdis; iexact HDis', 'rfl']
    SPECIAL[ZL] = dict(
        doc='''Its fact (`zerologInit`, `Base.lean`): `gLevel`'s cell in an invariant, `LevelFieldName`,
`LevelFieldMarshalFunc` with its spec on the five levels, `enc`, `eventPool`'s `sync.Pool` of events and
`ioutil.Discard`'s value, read-only for good. Its initializer allocates its translated variables, initializes its imports,
runs their translated initializers (constants, function literals, `sync.Pool` literals, `new(int32)`)
and its two translated `init`s: `init.0` (`ctx.go`: `SetGlobalLevel(TraceLevel)`, `disabledLogger =
&Nop()`) and `init.1` (`encoder_json.go`), which stores a closure in `internal/json`'s
`JSONMarshalFunc`, another package's variable: through `internal/json`'s invariant, lending the
initializer's package state (`EtcdGrove.grpcInternal.wp_store_hook`). (dsv-retire-3, 2026-11-26: until
then names only, its `wp_initialize'` a trust-boundary axiom.)''',
        alloc_types={'arrayPool': 'Loc', 'consoleBufPool': '_root_.Perennial.sync.Pool',
                     'th': f'_root_.Perennial.{ZL}.timestampHook', 'disabledLogger': 'Loc',
                     'enc': f'_root_.Perennial.{ZJ}.Encoder', 'eventPool': 'Loc',
                     **{x: 'GoString' for x in ['TimestampFieldName', 'LevelFieldName', 'LevelTraceValue',
                                                'LevelDebugValue', 'LevelInfoValue', 'LevelWarnValue',
                                                'LevelErrorValue', 'LevelFatalValue', 'LevelPanicValue',
                                                'MessageFieldName', 'ErrorFieldName', 'CallerFieldName',
                                                'ErrorStackFieldName', 'TimeFieldFormat']},
                     **{x: 'GoFunc' for x in ['LevelFieldMarshalFunc', 'CallerMarshalFunc', 'ErrorStackMarshaler',
                                              'ErrorMarshalFunc', 'InterfaceMarshalFunc', 'TimestampFunc',
                                              'ErrorHandler']},
                     'CallerSkipFrameCount': 'w64', 'DurationFieldUnit': 'w64', 'DurationFieldInteger': 'Bool',
                     'gLevel': 'Loc', 'disableSampling': 'Loc', 'Often': 'w32', 'Sometimes': 'w32',
                     'Rarely': 'w32'},
        imports=['Dsverify.Proof.github_com.rs.zerolog.NewNil'],
        # the translated variable initializers: constants, function literals (`recv_eq_func_mk`), the
        # `sync.Pool` literals, `new(int32)`s
        before={'arrayPool': ['repeat (first | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto) | (wp_func_lits; wp_auto) | wp_auto)'],
                # `gLevel`'s cell (`new(int32)`, shadowed by `disableSampling`'s), named for `SetGlobalLevel`
                # and `eventPool`'s `sync.Pool` (`new(Pool)`'s cell), for the fact
                '$inits': ['rename_i _ pep pgl', 'irename: (pgl ↦ (_ : w32) : IProp GF) => HgCell',
                           'irename: (pep ↦ (_ : _root_.Perennial.sync.Pool) : IProp GF) => HepCell']},
        after={'init.«0»': [
            "-- `SetGlobalLevel(TraceLevel)`: the atomic store into `gLevel`'s cell, owned here",
            'unfold TraceLevel',
            'wp_func_call',
            'wp_call',
            'try wp_auto',
            'wp_apply_core sync.atomic.wp_StoreInt32 $$ [] [-]',
            '· iexact {Hd:sync.atomic}',
            'iapply fupd_mask_intro Std.LawfulSet.empty_subset',
            'iintro Hmask',
            'inext',
            'iexists _',
            'iframe HgCell',
            'iintro HgCell',
            'imod Hmask with -',
            'imodintro',
            'try wp_auto',
            "-- `Nop()`: `New(nil).Level(Disabled)`; `New(nil)` reads `ioutil.Discard` (io/ioutil's fact)",
            'ihave #ID : (∃ w : GoInterface, globalAddr _root_.Perennial.io.ioutil.Discard ↦□ w : IProp GF) $$ []',
            '· iapply isPkgInit_access $$ {Hd:io.ioutil}',
            'icases ID with ⟨%wdis, #HDis⟩',
            'wp_apply (wp_Nop wdis) $$ HDis as %lnop -',
            'try wp_auto'] + ZL_FACT,
            'init.«1»': [
            f'ihave #Hfj : (_root_.Perennial.{ZJ}.jsonInit (hG := hG) : IProp GF) $$ []',
            f'· iapply isPkgInit_access $$ {{Hd:{ZJ}}}',
            'try wp_auto',
            f'unfold _root_.Perennial.{ZJ}.jsonInit',
            'icases Hfj with ⟨#Hfc, -⟩',
            'wp_apply (EtcdGrove.grpcInternal.wp_store_hook (hG := hG) (V := GoFunc) _ _ _ _) $$ [Hfc Hown] as Hown',
            '· iframe Hown Hfc',
            'try wp_auto']},
        finish=g.FIN_PRE[:6] + ZL_FIN,
    )
    return SPECIAL


# etc/dsv/kitgen.py (notes/dsv-kitgen.md): the kit's generated plumbing, as paxos's
_MAINS_VARS = '''variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.{n}.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]'''

KITGEN = dict(
    name='rabia',
    go_module_dir=os.path.join('examples', 'dsverify', 'rabia'),
    go_pkg_dir=os.path.join('examples', 'rabianet'),
    go_import='rabia/examples/rabianet',
    go_pkg='rabianet',
    lean_pkg='rabia.examples.rabianet',
    proof_roots=['rabia'],
    roles=[
        dict(cmd='orch', go_doc="the rabia kit's orchestrator machine", go_call='Orch()',
             share='''orchCore (G := G) γ ∗ ([∗list] a ∈ (List.range nC).map cliAddr, remoteAddr (Gg := G) (kvR γ) a) ∗ mapCtx (Gg := G) (I := KIn) ∗ pendCtx (Gg := G) (kvR γ) (kvS0 (GF := remoteGF)) γp ∗ pendLib (Gg := G) (kvS0 (GF := remoteGF)) γp (kvS0 (GF := remoteGF)).M.init ∗ [∗list] a ∈ (List.range nC).map cliAddr, budUnits (Gg := G) a 24''',
             intro='⟨Hoc0, #Has, #Hmap0, #Hpend0, Hlib0, Hbud0⟩',
             main='fun σ0 => cmd.{n}.wp_main (wp_Orch (wp_Codec) (wp_gens)) γ γp hrb σ0',
             frame='Hoc0 Hlib0 Hbud0', split='Hoc Hlib Hbud',
             wp_main='''theorem wp_main (wp_Orch : rabianet.Orch.spec (GF := GF) (hG := hG)) (γ : Names)
    (γp : PendNames) (hrb : receiptBound GF ≤ 2 ^ 63) (σ : GMap GoString Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗ (orchCore γ ∗
        ([∗list] a ∈ (List.range nC).map cliAddr, remoteAddr (Gg := hG.goose_globalGS) (kvR γ) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) ∗
        pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS0 (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init ∗
        [∗list] a ∈ (List.range nC).map cliAddr, budUnits (Gg := hG.goose_globalGS) a 24) ∗
        ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨⟨Hcore, #Has, #Hmap, #Hpend, Hlib, Hbud⟩, -⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.{pkg}) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Orch γ γp hrb $$ [Hcore Hlib Hbud]
  · iframe #
    iframe Hcore Hlib Hbud
  iapply HΦ
  itrivial

'''),
        dict(cmd='client{id}', ids=list(range(6)), go_doc="the rabia kit's client machine {id}",
             go_call='Client({id})',
             share='''cliCore (G := G) γ {id} ∗ remoteAddr (Gg := G) (kvR γ) (cliAddr {id}) ∗ mapCtx (Gg := G) (I := KIn)''',
             intro='⟨Hc, #Hra0, #Hmap0⟩', main='fun σ0 => cmd.{n}.wp_main (wp_Client (wp_Codec)) γ σ0',
             frame='Hc', split='Hc{id}',
             wp_main='''theorem wp_main (wp_Client : rabianet.Client.spec (GF := GF) (hG := hG)) (γ : Names)
    (σ : GMap GoString Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗ (cliCore γ {id} ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR γ) (cliAddr {id}) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn)) ∗
        ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨⟨Hcore, #Hra, #Hmap⟩, Hσ⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.{pkg}) $$ []
  · iPkgInit
  (try wp_auto)
  have h := wp_Client γ {id} σ (by decide)
  rw [show (W64 (({id} : Nat) : Int)) = W64 {id} from rfl] at h
  wp_apply h $$ [Hcore Hσ] as %hf
  · iframe #
    iframe Hcore Hσ
  exact hf.elim

'''),
        dict(cmd='server{id}', ids=list(range(1, 6)), go_doc="the rabia kit's server machine {id}",
             go_call='Server({id})',
             share='serverShare (G := G) γ {k}', intro='Hsh', main='fun σ0 => cmd.{n}.wp_main wp_Server γ σ0',
             frame='Hsh', split='Hs{k}',
             wp_main='''theorem wp_main (wp_Server : rabianet.Server.spec (GF := GF)) (γ : Names)
    (σ : GMap GoString Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗ serverShare γ {k} ∗
        ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hσ⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.{pkg}) $$ []
  · iPkgInit
  (try wp_auto)
  have h := wp_Server γ {k} σ (by decide)
  rw [show (W64 (({k} + 1 : Nat) : Int)) = W64 {id} from rfl] at h
  wp_apply h $$ [Hsh Hσ] as %hf
  · iframe #
    iframe Hsh Hσ
  exact hf.elim

'''),
    ],
    statement=dict(
        theorem='rabia_remote_robust',
        doc='''**The rabia kit, closed** (dsverify-lab's rabia-r1wake-1 on examples/lib/remote; notes/dsv-rabia.md):
twelve machines, none of which crashes -- the orchestrator (chooses a configuration at random and
sends it to every client machine and to the servers it names, then `remote.Check` of six clients'
eight operations against the key-value map with pending puts), six client machines (each waits for
the configuration, configures Rabia and connects its Rabia client endpoint, then
`remote.ServeClient`) and five server machines (each waits for the configuration and, if it is one
of its `n` servers, runs a Rabia server; rabia over TCP) -- deployed at `rabiaKitAddrs`
(`DistDeploy`: the addresses distinct and valid, no connection, no listener). In every execution
of fewer than `remoteStepBound` (`2 ^ 63`) steps, with any number of threads, no thread of any machine is stuck and none
has a top-level panic (`Robust`, `Robustness/Statement.lean`). Since the orchestrator panics unless
porcupine accepts the history, this says porcupine accepts every history, under every fault the
net extension allows.

**Premise** (at the bundle `remoteGF` the proof uses, for every machine's heap): go-redis v8's
initializer runs without panicking (`InitHyp`; its axiom review refuted it as an axiom,
`notes/axiom-review/dsv-inits/github-com-go-redis-redis-v8.md`). Not premises: the functions of the
libraries translated with names only (zerolog's `New(nil)`, a logger's levels, events and `Msg`; gogo `proto`'s
`Register*` calls in `message`'s initialization; math/rand's `NewSource`/`New`/`(*rngSource).Int63`)
and the environment claim that nobody sends SIGINT or SIGTERM to the deployment's processes
(`signal.Notify(c, SIGINT, SIGTERM)` registers a channel that never receives) are per-function
trust-boundary axioms, and so are the initializers of zerolog, gogo `proto`, `gogoproto` and
`os/signal` (their `wp_initialize'`); every axiom the result rests on is listed in
`etc/tcb-collections/dsv-rabia.txt`. `log.Println` is proved from Perennial's trusted model of
`log`; `math/rand`'s initializer, package-level `Intn` and `(*Rand).Intn` from Perennial's code.
Proved in
`Dsverify/Proof/rabia/examples/rabianet/TopLevelRobustness.lean`.''',
        imports=['public import Net.Statement.DistDeploy', 'public import Robustness.Statement', 'public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared', 'public import Dsverify.Proof.github_com.go_redis.redis.v8.Init'],
        opens=['open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)'],
        heap_at='spec',
        heap_at_doc='''A machine's heap over `remoteGF` at the deployment's Go local context `lctx` (the heaps the
proof makes, one per machine): the global ghost state `G` and the local `L`, its local context
`lctx`. The premises below hold of every such heap.''',
        addrs='rabiaKitAddrs', steps='remoteStepBound',
        premises=[('hri', 'github_com.go_redis.redis.v8.InitHyp')],
        # (dsv-fix4) the library classes the proof discharges from per-function axioms
        discharged=[('github_com.gogo.protobuf.proto.Hyps', 'github_com.gogo.protobuf.proto.hyps_holds'),
                    ('github_com.rs.zerolog.Hyps', 'github_com.rs.zerolog.hyps_holds'),
                    ('math.rand.Hyps', 'math.rand.rng.hyps_holds'),
                    ('os.signal.NoSignals os.signal.quietSigs', '⟨os.signal.Notify.wp_proofQuietSigs⟩')],
    ),
    defs=dict(
        doc='''The rabia kit's deployment (notes/dsv-rabia.md): its twelve machines' boot programs and addresses,
the definitions its top-level statement (`Spec/rabia/examples/rabianet/TopLevelRobustness.lean`)
names (as paxos's `TopLevelDefs.lean`).''',
        imports=['public import Dsverify.Proof.rabia.Core.Proto'],
        options=[],
        system_doc='''The system: the twelve machines, from the local states `σ i`: the orchestrator, client
machines 0..5, server machines 1..5 (each a command of `examples/rabianet/cmd`).''',
        addrs_def='''/-- The deployment's addresses: the server machines' proxy, network and configuration addresses
and the client machines' configuration addresses (`protoAddrs`, `Core/Proto.lean`), then the client
machines' addresses for the orchestrator's calls (`ClientAddrs()`). -/
def rabiaKitAddrs : List GoString := protoAddrs ++ (List.range nC).map cliAddr''',
    ),
    proof=dict(
        doc='''The rabia kit's top-level result (`Spec/rabia/examples/rabianet/TopLevelRobustness.lean`), proved
(as paxos's): from the deployment's start (the protocol library's registry and the addresses unset),
the ghost start (`Core/Start.lean`'s `start`: the shares, the key-value state, the client machines'
addresses still unset), remote's map of operations, the client machines' addresses' protocols
(remote's request and reply protocols for `kvR γ`), remote's pending library over the key-value
state, and each machine's boot program from its share, through `robust_of_distProtoRB`. The boot
(`wp_boot`) hands `main` the machine's package state after the initialization (`ownGoState`, out
of `ownInitializing`): the clients and servers claim `config.Conf` with it.''',
        imports=['public import Dsverify.Proof.rabia.examples.rabianet.Linked', 'public import Dsverify.Proof.rabia.examples.rabianet.CodecProof', 'public import Dsverify.Proof.rabia.Core.Start', 'public import Net.Statement.DistBridge', 'public import Dsverify.Proof.github_com.gogo.protobuf.proto.HypsHoldLinked', 'public import Dsverify.Proof.github_com.rs.zerolog.HypsHoldLinked', 'public import Dsverify.Proof.math.rand.RandsLinked', 'public import Dsverify.Proof.os.signal.Notify'],
        options=['set_option linter.unusedSectionVars false', 'set_option maxRecDepth 100000'],
        opens=['open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote rabia', 'open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)'],
        boot='gostate',
        boot_doc='''/-- A command's boot program, from its initializer's spec (with the program's package table
`getIs`) and a spec of its `main` with precondition `P` and the machine's package state after the
initialization (paxos's `wp_boot` drops it). -/''',
        head='''/-- The rabia kit, from the codec's and the generator's specs (closed below). -/
theorem rabia_remote_robust_of (wp_Codec : ∀ [GoGlobalContext] [hG : HeapGS HasLC.hasLC remoteGF]
      [go.Semantics] [rabia.examples.rabianet.Assumptions] [go.BasicIntoValInj] [NetProtoGS]
      [RemoteGS], Codec.spec (GF := remoteGF) (hG := hG))
    (wp_gens : ∀ [GoGlobalContext] [hG : HeapGS HasLC.hasLC remoteGF]
      [go.Semantics] [rabia.examples.rabianet.Assumptions] [go.BasicIntoValInj] [NetProtoGS]
      [RemoteGS], gens.spec (GF := remoteGF) (hG := hG)) :
    rabia_remote_robust.spec := by''',
        start='''  iintro #Hreg Hs
  unfold rabiaKitAddrs
  imod start (G := G) $$ Hreg Hs with ⟨%γ, Hoc, Hcs, Hss, Hkv, Hun⟩
  imod mapCtx_alloc (Gg := G) (I := KIn) ⊤ ((List.range nC).map cliAddr) 24 (by decide)
    with ⟨%ρ, -, #Hmap, Hbud⟩
  imod addrs_set_proto (Gg := G) ⊤ (fun a => github_com.mit_pdos.etcd_grove.examples.lib.remote.reqP (Gg := G) (RBase.svc (kvR γ)) a)
    (fun _ => github_com.mit_pdos.etcd_grove.examples.lib.remote.repP (Gg := G) (RBase.svc (kvR γ))) ((List.range nC).map cliAddr) $$ Hreg Hun with #Hpc
  have hv : kvState (G := G) γ.rab (model.kv GoString GoString).init ⊢
      (kvR (Gg := G) γ).sysState (kvR (Gg := G) γ).B.init := .rfl
  ihave Hkv := hv $$ Hkv
  imod pend_alloc (Gg := G) (kvR γ) ⊤ (kvS0 (GF := remoteGF)) rfl $$ Hkv with ⟨%γp, #Hpend, Hlib⟩
  ihave #Hra : [∗list] a ∈ (List.range nC).map cliAddr, remoteAddr (Gg := G) (kvR γ) a $$ [Hpc]
  · unfold remoteAddr svcAddr; iexact Hpc
  ihave Hcs : [∗list] c ∈ [0, 1, 2, 3, 4, 5], cliCore (G := G) γ c $$ [Hcs]
  · rw [← range_nC]; iexact Hcs
  ihave Hss : [∗list] k ∈ [0, 1, 2, 3, 4], serverShare (G := G) γ k $$ [Hss]
  · rw [← range_maxS']; iexact Hss
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc0, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc1, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc2, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc3, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc4, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc5, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs0, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs1, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs2, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs3, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs4, Hss⟩
  ihave #Hra0 : remoteAddr (Gg := G) (kvR γ) (cliAddr 0) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 0) rfl $$ Hra
  ihave #Hra1 : remoteAddr (Gg := G) (kvR γ) (cliAddr 1) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 1) rfl $$ Hra
  ihave #Hra2 : remoteAddr (Gg := G) (kvR γ) (cliAddr 2) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 2) rfl $$ Hra
  ihave #Hra3 : remoteAddr (Gg := G) (kvR γ) (cliAddr 3) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 3) rfl $$ Hra
  ihave #Hra4 : remoteAddr (Gg := G) (kvR γ) (cliAddr 4) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 4) rfl $$ Hra
  ihave #Hra5 : remoteAddr (Gg := G) (kvR γ) (cliAddr 5) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5) rfl $$ Hra''',
        tail='''/-- **The rabia kit, closed** (see the statement's file). -/
theorem rabia_remote_robust : rabia_remote_robust.spec :=
  rabia_remote_robust_of Codec.wp_proof gens.wp_proof
''',
    ),
    mains=dict(
        doc='''The rabia kit's twelve commands' `main`s (`examples/rabianet/cmd/*`), each its kit function on its
constants, from the kit functions' specs (`OrchProof.lean`, `ClientProof.lean`,
`ServerProof.lean`). Each `main` gets its machine's package state `ownGoState σ` after the
initialization (the top level's boot hands it over): the clients and servers claim `config.Conf`
with it.''',
        imports=['public import Dsverify.Proof.rabia.examples.rabianet.KitSpecs'],
        options=['set_option linter.unusedSectionVars false'],
        opens=['open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net', 'open github_com.mit_pdos.etcd_grove.examples.lib.remote rabia rabia.examples.rabianet'],
        variables=_MAINS_VARS,
    ),
)
