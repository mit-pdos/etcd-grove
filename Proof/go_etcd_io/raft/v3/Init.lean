/-
Lean-first (no Rocq counterpart).

# Package initialization of `go.etcd.io/raft/v3` and its subpackages (2026-10-12)

The `wp_initialize'` of raft, `quorum`, `tracker` and `confchange`, from their initializers:
each initializes its imports and runs its package-level variable initializers, and gives
the package's `isPkgInit` (`Base.lean`). For raft that is `isInitialized`: the error
variables (non-`nil`, and for the three the proofs compare against, of a pointer type, from
`errors.New`), `globalRand` with its mutex, `emptyState`, the message tables.

Three things are not facts of the model, and are premises:
* `raftpb`'s, `os`'s, `reflect`'s and `strconv`'s `wp_initialize'` are `sorry`: their
  initializers are only partly translated (the variables' initializers that `raftpb.toml`
  does not translate, gogoproto's registration in `raftpb`'s `init`, and the names-only
  standard-library packages), so they call opaque values.
* `log.New` (raft's `defaultLogger`, `discardLogger`) is not modelled by Perennial: the
  class `log.NewModel` says that the name `log.New` stands for `log.New.model`, a function
  that returns a new `*Logger` (what raft needs of it; the Go function allocates and
  initializes a `Logger`, without failing).
* `context`'s initializer needs `context.ErrorStringIsError`, a method-set fact
  (`Perennial/Proof/context_proof/context_init.lean`).
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import Perennial.Proof.context_proof.context_init

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
def New.model [FfiSyntax] [GoGlobalContext] : val :=
  λ: "out" "prefix" "flag", Alloc (Val #())

/-- The name `log.New` stands for `New.model`: an assumption about the semantics, like the
`FuncUnfold` fields of a package's `Assumptions` (Perennial translates `log` without
`New`). -/
class NewModel [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  New_unfold : FuncUnfold log.New [] New.model

attribute [instance] NewModel.New_unfold

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem reflect.wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.reflect get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val reflect.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.reflect }} := by
  -- Unprovable: `reflect` is translated names-only; its variables' initializers
  -- (`uint8Type'init`, `kindNames'init`, ...) are opaque (axioms in Perennial/Code/reflect.lean).
  sorry

theorem os.wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val os.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.os }} := by
  -- Unprovable: `os` is translated names-only; its variables' initializers (`Stdin'init`,
  -- `Stdout'init`, `Stderr'init`, `ErrInvalid'init`, ...) are opaque (axioms in
  -- Perennial/Code/os.lean).
  sorry

theorem strconv.wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.strconv get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val strconv.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.strconv }} := by
  -- Unprovable: `strconv` is translated names-only; its variables' initializers
  -- (`ErrRange'init`, `ErrSyntax'init`, the `isPrint` tables) are opaque (axioms in
  -- Perennial/Code/strconv.lean).
  sorry

theorem go_etcd_io.raft.v3.raftpb.wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.raftpb get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val go_etcd_io.raft.v3.raftpb.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }} := by
  -- Unprovable: `raftpb.toml` translates the types and the functions raft's proofs use,
  -- not the generated protobuf code: the initializers of `ErrInvalidLengthRaft`,
  -- `ErrIntOverflowRaft`, `ErrUnexpectedEndOfGroupRaft` (`fmt.Errorf`), of the file
  -- descriptor, of `_ = proto.Marshal`, and the package's `init` (gogoproto's `RegisterEnum`,
  -- `RegisterType`, `RegisterFile`) are opaque (axioms in Code/go_etcd_io/raft/v3/raftpb.lean).
  sorry

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

end init

namespace go_etcd_io.raft.v3

section raft_init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [context.ErrorStringIsError] [log.NewModel]

theorem os_isPkgInit_Stderr :
    isPkgInit (PROP := IProp GF) pkg_id.os ⊢
      ∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.os

theorem io_isPkgInit_Discard :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢
      ∃ w : GoInterface, typedPointsto (globalAddr io.Discard) w DFrac.discard := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.io

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
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSnapOutOfDate go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCompacted go.error as HEC
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStepPeerNotFound go.error as HESP
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStepLocalMsg go.error as HESL
  wp_apply wp_GlobalAlloc (V := GoInterface) errBreak go.error as _
  wp_apply wp_GlobalAlloc (V := GoArray GoString 4) stmap _ as _
  wp_apply wp_GlobalAlloc (V := Loc) globalRand _ as HGR
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrProposalDropped go.error as HEPD
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStopped go.error as HES
  wp_apply wp_GlobalAlloc (V := raftpb.HardState) emptyState _ as HEmpty
  wp_apply wp_GlobalAlloc (V := GoInterface) raftLogger Logger.ty as _
  wp_apply wp_GlobalAlloc (V := sync.Mutex) raftLoggerMu _ as _
  wp_apply wp_GlobalAlloc (V := Loc) discardLogger _ as _
  wp_apply wp_GlobalAlloc (V := Loc) defaultLogger _ as _
  wp_apply encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply go_etcd_io.raft.v3.tracker.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply go_etcd_io.raft.v3.quorum.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply go_etcd_io.raft.v3.confchange.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply slices.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply math.big.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply crypto.rand.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply os.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply log.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply io.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply fmt.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  icases os_isPkgInit_Stderr $$ Hd6 with ⟨%stderr, #Hstderr⟩
  icases io_isPkgInit_Discard $$ Hd4 with ⟨%discard, #Hdiscard⟩
  iapply wp_fupd
  repeat (first
    | (wp_apply log.wp_New as %_ _)
    | (wp_apply errors.wp_New_ptr as %_ #_)
    | wp_auto)
  iStructNamed «$r0»
  imod sync.init_Mutex iprop(True) ⊤ («$r0_ptr».[lockedRand, go!"mu"]) $$ mu [] with #Hmu
  · inext
    itrivial
  ipersist HES
  ipersist HEPD
  ipersist HGR
  ipersist HEmpty
  ipersist HEC
  ipersist HEU
  ipersist HESU
  ipersist HESP
  ipersist HESL
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
  rw [show (⟨W64 0, W64 0, W64 0⟩ : raftpb.HardState) = zero_val raftpb.HardState from rfl]
  iframe HES HEPD HGR HEmpty HEC HEU HESU HESP HESL HisLocal HisResp Hmu
  ipureintro
  exact ⟨nofun, nofun, ⟨_, _, rfl⟩, nofun, nofun, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, nofun⟩

end raft_init

end go_etcd_io.raft.v3

end Perennial
