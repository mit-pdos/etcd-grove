/-
Lean-first (no Rocq counterpart).

# Package initialization of `go.etcd.io/raft/v3` and its subpackages (2026-10-12)

The `wp_initialize'` of raft, `quorum`, `tracker` and `confchange`, from their initializers:
each initializes its imports and runs its package-level variable initializers, and gives
the package's `isPkgInit` (`Base.lean`). For raft that is `isInitialized`: the error
variables (non-`nil`, and for the three the proofs compare against, of a pointer type, from
`errors.New`), `globalRand` with its mutex, `emptyState`, the message tables.

Three things are not facts of the model, and are premises:
* `os`'s initializer is only partly translated (the standard library's names-only `os`,
  Perennial's, whose initializers with translated callees are translated since Perennial
  `11ac2f242`, so `os.wp_initialize'` initializes `io/fs`, `sync` and `errors`; `strconv`'s is Perennial's own since it translates `strconv`, 24bef275e), so it calls opaque values `X.init`: the
  trust-boundary axioms `<pkg>.opaqueInitsOk` say these run (the generated `Init.lean` files'
  method, `etc/gen-init.py`), `os.initFuncsOk` that its untranslated `func init()`s (`init.0`, as
  gc names it) return (2026-10-19, when Goose began calling a package's `init`s by name), and
  `os.Stderr_init` that `Stderr`'s gives the variable some `*File`, which `os`'s fact reads
  (2026-10-18; until then the four `wp_initialize'` were `sorry`). `raftpb`'s and `proto`'s
  untranslated initializers and `init`s are trusted no-op models (2026-10-20, until then axioms
  like these: `TrustedCode/go_etcd_io/raft/v3/raftpb.lean`,
  `TrustedCode/google_golang_org/protobuf/proto.lean`), and raftpb's descriptor tables
  `file_raft_proto_goTypes` and `_depIdxs` are translated. `raftpb`'s and `proto`'s call the
  generated `protoreflect`/`protoimpl` theorems, so they (and `quorum`'s, `tracker`'s,
  `confchange`'s) are stated at `HasLC.hasLC`, with their package's `Assumptions`.
  (Raft v3.7, stage R4: `proto` is new, raft imports it; `reflect` is gone, `ConfState.Equivalent`
  no longer calling `reflect.DeepEqual`; `emptyState` is a pointer, `&pb.HardState{}`.)
* `log.New` (raft's `defaultLogger`, `discardLogger`) is not modelled by Perennial: the
  class `log.NewModel` says that the name `log.New` stands for `log.New.model`, a function
  that returns a new `*Logger` (what raft needs of it; the Go function allocates and
  initializes a `Logger`, without failing).
-/
module

public import Perennial.Proof.strconv.Link
public import Proof.go_etcd_io.raft.v3.Base
public import Perennial.Proof.context
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.io.fs
public import Perennial.Proof.syscall.Link
public import Perennial.Proof.internal.poll.Link
public import Perennial.Proof.os.Models
public import Perennial.Proof.errors.NewVar
public import Proof.google_golang_org.protobuf.reflect.protoreflect.Init
public import Proof.google_golang_org.protobuf.runtime.protoimpl.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace log

/-- A model of `log.New(out, prefix, flag)`: a fresh pointer. `Logger` is an opaque type in
Perennial's `log` (no layout, so no typed allocation), and raft only stores the pointer (in
`DefaultLogger`, whose methods the register's `quietLogger` replaces), so the model
allocates an untyped cell: what Go returns is a fresh, non-`nil` `*Logger`. -/
def New.model [GooseExts] [GoGlobalContext] : val :=
  λ: "out" "prefix" "flag", Alloc (Val #())

/-- The name `log.New` stands for `New.model`: an assumption about the semantics, like the
`FuncUnfold` fields of a package's `Assumptions` (Perennial translates `log` without
`New`). -/
class NewModel [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  New_unfold : FuncUnfold log.New [] New.model

attribute [instance] NewModel.New_unfold

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions] [NewModel]

theorem wp_New (out : GoInterface) (pfx : GoString) (flag : w64) :
    {{ (True : IProp GF) }}
      (App (App (App (Val (@! log.New)) (Val #out)) (Val #pfx)) (Val #flag))
    {{ (l : Loc), RET #l; True }} := by
  wp_start
  wp_apply (wp_alloc_untyped _ (isPanic_intoVal _)) as %l Hl
  iapply HΦ
  itrivial

end wps

end log



/-- `x ∈ [a, ..., x, ...]`, linear in the list. -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit package_sem in
/-- `internal/poll`'s fact (`isInit`), as `io.fs.isInit_access`. -/
theorem internal_poll_isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢ internal.poll.isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll

omit package_sem in
theorem os.wp_initialize' [os.Assumptions] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val os.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.os }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoFunc) os.pollSplice _ as _
  wp_apply wp_GlobalAlloc (V := GoFunc) os.pollCopyFileRange _ as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.errPatternHasSeparator go.error as _
  wp_apply wp_GlobalAlloc (V := GoSlice) os.Args _ as _
  wp_apply wp_GlobalAlloc (V := GoFunc) os.checkPidfdOnce _ as _
  wp_apply wp_GlobalAlloc (V := Bool) os.checkWrapErr go.bool as _
  wp_apply wp_GlobalAlloc (V := GoFunc) os.lstat _ as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.errPathEscapes go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.errWriteAtInAppendMode go.error as _
  wp_apply wp_GlobalAlloc (V := os.Signal) os.Kill _ as _
  wp_apply wp_GlobalAlloc (V := os.Signal) os.Interrupt _ as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrNoHandle go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.errProcessReleased go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrProcessDone go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrDeadlineExceeded go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrNoDeadline go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrClosed go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrNotExist go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrExist go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrPermission go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) os.ErrInvalid go.error as _
  wp_apply wp_GlobalAlloc (V := sync.Pool) os.dirBufPool sync.Pool.ty as _
  wp_apply errors.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply internal.poll.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hpoll⟩
  wp_apply syscall.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsys⟩
  wp_apply sync.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply io.fs.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hfs⟩
  -- `ErrInvalid = fs.ErrInvalid`, ...: io/fs's error variables, which its fact gives
  ihave #Hfsi := io.fs.isInit_access $$ Hfs
  icases Hfsi with ⟨#VIn, #VPe, #VEx, #VNE, #VCl, -⟩
  iunfold errors.newVar at VIn VPe VEx VNE VCl
  icases VIn with ⟨%_, #_, -⟩
  icases VPe with ⟨%_, #_, -⟩
  icases VEx with ⟨%_, #_, -⟩
  icases VNE with ⟨%_, #_, -⟩
  icases VCl with ⟨%_, #_, -⟩
  -- `ErrNoDeadline = errNoDeadline()`, ...: internal/poll's, which its fact gives
  ihave #Hpi := internal_poll_isInit_access $$ Hpoll
  icases Hpi with ⟨#HpN, ⟨%_, #_⟩⟩
  iunfold errors.newVar at HpN
  icases HpN with ⟨%_, #_, -⟩
  -- `dirBufPool`'s `New`, a function literal
  rw [recv_eq_func_mk BAnon BAnon]
  wp_auto
  -- `errNoDeadline()`, `errDeadlineExceeded()`: internal/poll's variables
  wp_func_call
  wp_call
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
  wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
  wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
  try wp_auto
  wp_apply os.wp_Stdin_init
  wp_apply os.wp_Stdout_init
  wp_apply os.wp_Stderr_init as ⟨%stderr, Hstderr⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
  wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
  try wp_auto
  -- `checkPidfdOnce = sync.OnceValue(checkPidfd)` (translated since Perennial `a2a531d4d`)
  wp_apply sync.wp_OnceValue $$ [$Hsync] as %_ -
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
  try wp_auto
  -- `func init() { Args = runtime_args() ... }` (`proc.go`), `runtime_args` a trusted model
  wp_func_call
  wp_call
  try wp_auto
  wp_func_call
  wp_apply os.wp_runtime_args_impl as %_ -
  try wp_auto
  ipersist Hstderr
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

end init

section init_lc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem google_golang_org.protobuf.proto.wp_initialize'
    [google_golang_org.protobuf.proto.Assumptions] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.protobuf.proto get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.protobuf.proto.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  -- (2026-10-22) `internal/pragma`, which `MarshalOptions` (translated since) names
  wp_apply google_golang_org.protobuf.internal.pragma.wp_initialize' _ Hinit.2.2.1 $$ Hown
    as ⟨Hown, #H0⟩
  wp_apply google_golang_org.protobuf.reflect.protoreflect.wp_initialize' _ Hinit.2.1 $$ Hown
    as ⟨Hown, #H1⟩
  -- errUnknown, errDecode, errRecursionDepth, wireTypes: their trusted initializers do nothing
  wp_call
  wp_call
  wp_call
  wp_call
  -- init.0: its trusted model does nothing
  wp_func_call
  wp_call
  iframe Hown
  is_pkg_init_finish

theorem go_etcd_io.raft.v3.raftpb.wp_initialize'
    [go_etcd_io.raft.v3.raftpb.Assumptions] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.raftpb get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val go_etcd_io.raft.v3.raftpb.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoSlice) go_etcd_io.raft.v3.raftpb.file_raft_proto_depIdxs _ as HdepIdxs
  wp_apply wp_GlobalAlloc (V := GoSlice) go_etcd_io.raft.v3.raftpb.file_raft_proto_goTypes _ as HgoTypes
  wp_apply wp_GlobalAlloc (V := Loc) go_etcd_io.raft.v3.raftpb.ConfChangeType_value _ as HConfChangeType_value
  wp_apply wp_GlobalAlloc (V := Loc) go_etcd_io.raft.v3.raftpb.ConfChangeType_name _ as HConfChangeType_name
  wp_apply wp_GlobalAlloc (V := Loc) go_etcd_io.raft.v3.raftpb.ConfChangeTransition_value _ as HConfChangeTransition_value
  wp_apply wp_GlobalAlloc (V := Loc) go_etcd_io.raft.v3.raftpb.ConfChangeTransition_name _ as HConfChangeTransition_name
  wp_apply wp_GlobalAlloc (V := Loc) go_etcd_io.raft.v3.raftpb.MessageType_value _ as HMessageType_value
  wp_apply wp_GlobalAlloc (V := Loc) go_etcd_io.raft.v3.raftpb.MessageType_name _ as HMessageType_name
  wp_apply wp_GlobalAlloc (V := Loc) go_etcd_io.raft.v3.raftpb.EntryType_value _ as HEntryType_value
  wp_apply wp_GlobalAlloc (V := Loc) go_etcd_io.raft.v3.raftpb.EntryType_name _ as HEntryType_name
  repeat (first
    | wp_apply google_golang_org.protobuf.runtime.protoimpl.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
    | wp_apply google_golang_org.protobuf.reflect.protoreflect.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
    | wp_apply slices.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
    | wp_apply google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
    | wp_apply strings.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply strconv.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply fmt.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_auto)
  wp_apply (wp_map_make1 (K := w32) (V := GoString) _ _) as %m0 Hm0
  repeat (first
    | wp_apply (wp_mapInsert (K := w32) (V := GoString) _ m0 _ _ _) $$ Hm0 as Hm0
    | wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := w32) _ _) as %m1 Hm1
  repeat (first
    | wp_apply (wp_mapInsert (K := GoString) (V := w32) _ m1 _ _ _) $$ Hm1 as Hm1
    | wp_auto)
  wp_apply (wp_map_make1 (K := w32) (V := GoString) _ _) as %m2 Hm2
  repeat (first
    | wp_apply (wp_mapInsert (K := w32) (V := GoString) _ m2 _ _ _) $$ Hm2 as Hm2
    | wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := w32) _ _) as %m3 Hm3
  repeat (first
    | wp_apply (wp_mapInsert (K := GoString) (V := w32) _ m3 _ _ _) $$ Hm3 as Hm3
    | wp_auto)
  wp_apply (wp_map_make1 (K := w32) (V := GoString) _ _) as %m4 Hm4
  repeat (first
    | wp_apply (wp_mapInsert (K := w32) (V := GoString) _ m4 _ _ _) $$ Hm4 as Hm4
    | wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := w32) _ _) as %m5 Hm5
  repeat (first
    | wp_apply (wp_mapInsert (K := GoString) (V := w32) _ m5 _ _ _) $$ Hm5 as Hm5
    | wp_auto)
  wp_apply (wp_map_make1 (K := w32) (V := GoString) _ _) as %m6 Hm6
  repeat (first
    | wp_apply (wp_mapInsert (K := w32) (V := GoString) _ m6 _ _ _) $$ Hm6 as Hm6
    | wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := w32) _ _) as %m7 Hm7
  repeat (first
    | wp_apply (wp_mapInsert (K := GoString) (V := w32) _ m7 _ _ _) $$ Hm7 as Hm7
    | wp_auto)
  -- file_raft_proto_enumTypes, _msgTypes: their trusted initializers do nothing
  wp_call
  wp_call
  -- file_raft_proto_goTypes, _depIdxs: translated slice literals, stored
  wp_apply wp_slice_literal (V := GoInterface) (t := go.any)
  try (isplitr; (ipureintro; rfl))
  iintro %goTypes ⟨-, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  wp_auto
  wp_apply wp_slice_literal (V := w32) (t := go.int32)
  try (isplitr; (ipureintro; rfl))
  iintro %depIdxs ⟨-, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  wp_auto
  -- init.0: its trusted model does nothing
  wp_func_call
  wp_call
  iframe Hown
  is_pkg_init_finish

end init_lc


section init2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem go_etcd_io.raft.v3.quorum.wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.quorum get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val go_etcd_io.raft.v3.quorum.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray w8 4) go_etcd_io.raft.v3.quorum._VoteResult_index _ as _
  wp_apply strconv.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
  wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
  wp_apply slices.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply math.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply fmt.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply cmp.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
  iframe Hown
  is_pkg_init_finish

theorem go_etcd_io.raft.v3.tracker.wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.tracker get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val go_etcd_io.raft.v3.tracker.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray GoString 3) go_etcd_io.raft.v3.tracker.prstmap _ as _
  wp_apply go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
  wp_apply go_etcd_io.raft.v3.quorum.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply strings.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply slices.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply fmt.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
  iframe Hown
  is_pkg_init_finish

theorem go_etcd_io.raft.v3.confchange.wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.confchange get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val go_etcd_io.raft.v3.confchange.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply go_etcd_io.raft.v3.tracker.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
  wp_apply go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
  wp_apply go_etcd_io.raft.v3.quorum.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply strings.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply fmt.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
  iframe Hown
  is_pkg_init_finish

end init2

namespace go_etcd_io.raft.v3

section raft_init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [log.NewModel]

/-- What `errors.wp_New_ptr` says of its error is what `IsNewError` asks. -/
theorem isNewError_of_ptr {ii : GoInterfaceOk} (h : errors.IsPointerError ii) :
    IsNewError (interface.ok ii) := by
  obtain ⟨T, l, h1, h2⟩ := h
  obtain ⟨ty, v⟩ := ii
  simp only at h1 h2
  subst h1 h2
  exact ⟨T, l, rfl⟩

theorem os_isPkgInit_Stderr :
    isPkgInit (PROP := IProp GF) pkg_id.os ⊢
      ∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.os

theorem io_isPkgInit_Discard :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢
      ∃ w : GoInterface, typedPointsto (globalAddr io.Discard) w DFrac.discard := by
  with_unfolding_all exact (isPkgInit_access (PROP := IProp GF) pkg_id.io).trans sep_elim_left

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray Bool 23) isResponseMsg _ as HisResp
  wp_apply wp_GlobalAlloc (V := GoArray Bool 23) isLocalMsg _ as HisLocal
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSnapshotTemporarilyUnavailable go.error as HESU
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnavailable go.error as HEU
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSnapOutOfDate go.error as HESOOD
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCompacted go.error as HEC
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStepPeerNotFound go.error as HESP
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStepLocalMsg go.error as HESL
  wp_apply wp_GlobalAlloc (V := GoInterface) errBreak go.error as HEB
  wp_apply wp_GlobalAlloc (V := GoArray GoString 4) stmap _ as _
  wp_apply wp_GlobalAlloc (V := Loc) globalRand _ as HGR
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrProposalDropped go.error as HEPD
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStopped go.error as HES
  wp_apply wp_GlobalAlloc (V := Loc) emptyState _ as HEmpty
  wp_apply wp_GlobalAlloc (V := GoInterface) raftLogger Logger.ty as _
  wp_apply wp_GlobalAlloc (V := sync.Mutex) raftLoggerMu _ as _
  wp_apply wp_GlobalAlloc (V := Loc) discardLogger _ as _
  wp_apply wp_GlobalAlloc (V := Loc) defaultLogger _ as _
  wp_apply encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply go_etcd_io.raft.v3.tracker.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply go_etcd_io.raft.v3.quorum.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply go_etcd_io.raft.v3.confchange.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply slices.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply math.big.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply crypto.rand.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply os.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply log.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply io.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply fmt.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hdp⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  icases os_isPkgInit_Stderr $$ Hd6 with ⟨%stderr, #Hstderr⟩
  icases io_isPkgInit_Discard $$ Hd4 with ⟨%discard, #Hdiscard⟩
  iapply wp_fupd
  repeat (first
    | (wp_apply log.wp_New as %_ _)
    | (wp_apply _root_.Perennial.context.wp_New_errorString as %_ ⟨-, #_⟩)
    | wp_auto)
  iStructNamed «$r0»
  imod sync.init_Mutex iprop(True) ⊤ («$r0_ptr».[lockedRand, go!"mu"]) $$ mu [] with #Hmu
  · inext
    itrivial
  -- (stage R4 phase 3) `emptyState`'s struct: its cells (all `nil`) frozen, its hidden fields
  -- made into the `protobuf` invariant (`hsRO es ⟨0, 0, 0⟩` unfolded, `Base.lean`)
  ihave %HesNN := typedPointsto_not_null $$ «$r0»
  icases typedPointsto_split _ _ _ $$ «$r0» with Hes
  simp only [TypedPointsto.typedPointstoDef]
  icases Hes with ⟨Hst, HeT, HeV, HeC, Heuf, Hesc, -⟩
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod inv_alloc (nroot.@"protobuf") ⊤
      iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32) (us : GoSlice),
        _.[raftpb.HardState, go!"state"] ↦ st ∗ _.[raftpb.HardState, go!"sizeCache"] ↦ sc ∗
          _.[raftpb.HardState, go!"unknownFields"] ↦ us ∗ us ↦* ([] : List w8))
      $$ [Hst Heuf Hesc Hnil] with #HesPb
  · inext
    iexists _, _, _
    iframe Hst Hesc Heuf Hnil
  ipersist HES
  ipersist HEPD
  ipersist HGR
  ipersist HEmpty
  ipersist HeT
  ipersist HeV
  ipersist HeC
  ipersist HEC
  ipersist HEU
  ipersist HESU
  ipersist HESP
  ipersist HESL
  ipersist HEB
  ipersist HESOOD
  ipersist HisLocal
  ipersist HisResp
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold isInitialized isLockedRand
  iexists _, _, _, _, _, _, _, _, _, _
  ihave #HEB' : iprop(∃ eb : GoInterface, (globalAddr errBreak ↦□ eb : IProp GF) ∗
      ⌜eb ≠ interface.nil ∧ IsNewError eb⌝) $$ [HEB]
  · iexists _
    iframe HEB
    ipureintro
    exact ⟨nofun, ⟨_, _, rfl⟩⟩
  -- (raft v3.7, stage R4) `emptyState = &pb.HardState{}`: a pointer to a fresh zero struct,
  -- as `hsRO es ⟨0, 0, 0⟩` unfolded (phase 3)
  ihave #HEmpty' : iprop(∃ es : Loc, (globalAddr emptyState ↦□ es : IProp GF) ∗ ⌜es ≠ null⌝ ∗
      (es.[raftpb.HardState, go!"Term"] ↦□ null : IProp GF) ∗
      (es.[raftpb.HardState, go!"Vote"] ↦□ null : IProp GF) ∗
      (es.[raftpb.HardState, go!"Commit"] ↦□ null : IProp GF) ∗
      inv (nroot.@"protobuf") iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
          (sc : w32) (us : GoSlice),
        es.[raftpb.HardState, go!"state"] ↦ st ∗ es.[raftpb.HardState, go!"sizeCache"] ↦ sc ∗
          es.[raftpb.HardState, go!"unknownFields"] ↦ us ∗ us ↦* ([] : List w8)))
      $$ [HEmpty HeT HeV HeC HesPb]
  · iexists _
    iframe HEmpty HeT HeV HeC HesPb
    ipureintro; exact HesNN
  ihave #HESOOD' : iprop(∃ e : GoInterface, (globalAddr ErrSnapOutOfDate ↦□ e : IProp GF))
      $$ [HESOOD]
  · iexists _; iexact HESOOD
  iframe HES HEPD HGR HEmpty' HEC HEU HESU HESP HESL HisLocal HisResp Hmu HEB' HESOOD'
  simp only [named, EtcdGrove.errorsNewVar]
  iframe #
  ipureintro
  exact ⟨nofun, nofun, ⟨_, _, rfl⟩, nofun, nofun,
    ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, nofun⟩

end raft_init

end go_etcd_io.raft.v3

end Perennial
