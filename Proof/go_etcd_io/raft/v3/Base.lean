/-
Port of etcd-grove's `new/proof/go_etcd_io/raft/v3_proof/base.v`: package
initialization instances for `go.etcd.io/raft/v3` and the packages it imports.

This replaces Perennial's `Perennial.Proof.go_etcd_io.raft.v3_proof.base` (the port of
upstream's `base.v`), which must not be imported alongside it: `IsPkgInit` has one
instance per package, and etcd-grove's raft instance is stronger.
The `wp_initialize'` of each of these packages, which establishes these predicates from
its initializer, is in `Init.lean` (2026-10-12; `raftpb`'s, `os`'s, `reflect`'s and
`strconv`'s are `sorry`: their initializers are only partly translated).

Lean notes: see Perennial's `base.lean` for the instances that live in other Perennial
files (`strings`, `math`, `bytes`, `log`, `io`, `errors`).
-/
module

public import Code.go_etcd_io.raft.v3
public import GeneratedProof.go_etcd_io.raft.v3
public import GeneratedProof.go_etcd_io.raft.v3.raftpb
public import Perennial.Code.reflect
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.context
public import Perennial.Proof.sync
public import Perennial.Proof.fmt
public import Perennial.Proof.slices_proof.slices_init
public import Perennial.Proof.cmp
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.strings
public import Perennial.Proof.math
public import Perennial.Proof.math.bits
public import Perennial.Proof.crypto.rand
public import Perennial.Proof.bytes
public import Perennial.Proof.log
public import Perennial.Proof.io
public import Perennial.Proof.errors
public import Perennial.Proof.sync_proof.mutex

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.raft.v3

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `reflect`, names-only (`raftpb`'s `ConfState.Equivalent` calls `reflect.DeepEqual`,
the axiom `Spec/reflect_DeepEqual.lean`). -/
instance reflect_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.reflect :=
  define_is_pkg_init iprop(True)
instance reflect_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.reflect :=
  build_get_is_pkg_init_wf

/-- gogoproto's `proto`, names-only (`raftpb`'s `ConfChangeV2.LeaveJoint` calls `proto.Equal`,
the axiom `Spec/github_com/gogo/protobuf/proto/Equal.lean`). -/
instance gogoproto_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.gogo.protobuf.proto :=
  define_is_pkg_init iprop(True)
instance gogoproto_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.gogo.protobuf.proto :=
  build_get_is_pkg_init_wf

instance raftpb_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  define_is_pkg_init iprop(True)
instance raftpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  build_get_is_pkg_init_wf

instance strconv_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.strconv :=
  define_is_pkg_init iprop(True)
instance strconv_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.strconv :=
  build_get_is_pkg_init_wf

instance quorum_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.quorum :=
  define_is_pkg_init iprop(True)
instance quorum_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.quorum :=
  build_get_is_pkg_init_wf

instance tracker_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.tracker :=
  define_is_pkg_init iprop(True)
instance tracker_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.tracker :=
  build_get_is_pkg_init_wf

instance confchange_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.confchange :=
  define_is_pkg_init iprop(True)
instance confchange_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.confchange :=
  build_get_is_pkg_init_wf

/-- `os`, names-only: its initialization is not modelled (its variables' initializers are
opaque, `Init.lean`), so this is what that initialization is assumed to give: `Stderr`
holds a fixed `*File`, which raft's initializer loads (`defaultLogger`). -/
instance os_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.os :=
  define_is_pkg_init iprop(∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard)
instance os_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.os :=
  build_get_is_pkg_init_wf

/-- `globalRand` is the package-level `*lockedRand` behind
`raft.resetRandomizedElectionTimeout`. Its one field, `mu`, is a `sync.Mutex` that
guards nothing the proof can see (`Intn` holds it across a `crypto/rand` call, whose
only state is the kernel's), so the lock invariant is `True`. The package initializer
installs `&lockedRand{}` (a zero `Mutex`), which is exactly what `init_Mutex` turns
into `isMutex … True`. -/
def isLockedRand (lr : Loc) : IProp GF :=
  iprop("#Hmu" ∷ sync.isMutex (lr.[lockedRand, go!"mu"]) iprop(True))

instance isLockedRand_persistent (lr : Loc) : Persistent (isLockedRand (GF := GF) lr) := by
  unfold isLockedRand; infer_instance

/-- An `error` value shaped the way `errors.New` builds one: an interface holding a
**pointer**.

Go's interface equality is not decidable on its own: `go_eq_interface` reduces
`i1 == i2` for two non-`nil` values to a comparison at the dynamic type after a
`CheckComparable`, which has a reduction only for the types Goose knows to be
comparable. For an *unknown* dynamic type there is none, so a proof that reaches
`err == ErrX` with `err` non-`nil` is **stuck**. That is exactly what
`raft.maybeSendSnapshot` does with `ErrSnapshotTemporarilyUnavailable`.

The claim is true of the value the package initializer installs: `errors.New` returns a
pointer converted to `error`. The type is left existential rather than pinned to
`errors.errorString`, because all the comparison needs is that it is *a* pointer type. -/
def IsNewError (e : GoInterface) : Prop :=
  ∃ (t : go.GoType) (p : Loc), e = interface.mkOk (go.GoType.PointerType t) #p

/-- etcd-grove's `isInitialized`: the package-level `error` variables the election
path compares against (each a non-nil interface value installed by the package
initializer; a proof that reads one needs the points-to, the load being through
`GlobalVarAddr`, and the disequality, to decide `err == ErrX` when `err` is `nil`), the
global RNG, and `emptyState`. -/
def isInitialized : IProp GF :=
  iprop(∃ (errStopped errCompacted errUnavailable errSnapUnavail errPropDropped : GoInterface)
      (globalRand' : Loc) (localMsgs responseMsgs : GoArray Bool 23)
      (errStepLocal errStepPeer : GoInterface),
    "ErrStopped" ∷ (globalAddr ErrStopped ↦□ errStopped : IProp GF) ∗
    "%HErrStopped" ∷ ⌜errStopped ≠ interface.nil⌝ ∗
    -- `maybeSendSnapshot` compares `Storage.Snapshot`'s error against this one; it is
    -- the only non-fatal error that method may return
    "ErrSnapUnavail" ∷ (globalAddr ErrSnapshotTemporarilyUnavailable ↦□ errSnapUnavail : IProp GF) ∗
    "%HErrSnapUnavail" ∷ ⌜errSnapUnavail ≠ interface.nil⌝ ∗
    -- and, unlike the others, it *compares* a non-`nil` error against it, which needs
    -- the dynamic type to be comparable (`IsNewError`)
    "%HErrSnapUnavail_new" ∷ ⌜IsNewError errSnapUnavail⌝ ∗
    "ErrCompacted" ∷ (globalAddr ErrCompacted ↦□ errCompacted : IProp GF) ∗
    "%HErrCompacted" ∷ ⌜errCompacted ≠ interface.nil⌝ ∗
    "ErrUnavailable" ∷ (globalAddr ErrUnavailable ↦□ errUnavailable : IProp GF) ∗
    "%HErrUnavailable" ∷ ⌜errUnavailable ≠ interface.nil⌝ ∗
    -- `raftLog.zeroTermOnOutOfBounds` compares a non-`nil` error (what `raftLog.term`
    -- returned) against both, which needs their dynamic types to be comparable --
    -- `IsNewError` above. Both are `errors.New(...)` in `storage.go`. Added 2026-10-01
    -- for `handleAppendEntries`'s reject path.
    "%HErrCompacted_new" ∷ ⌜IsNewError errCompacted⌝ ∗
    "%HErrUnavailable_new" ∷ ⌜IsNewError errUnavailable⌝ ∗
    -- `ErrProposalDropped = errors.New("raft proposal dropped")` (`raft.go`), which
    -- `stepFollower`/`stepCandidate` return for a proposal they cannot forward. Only
    -- loaded and returned, never compared, so no `IsNewError`. Added 2026-10-01.
    "ErrPropDropped" ∷ (globalAddr ErrProposalDropped ↦□ errPropDropped : IProp GF) ∗
    "%HErrPropDropped" ∷ ⌜errPropDropped ≠ interface.nil⌝ ∗
    -- the global RNG: the pointer, and the mutex behind it
    "#globalRand" ∷ (globalAddr globalRand ↦□ globalRand' : IProp GF) ∗
    "#HglobalRand" ∷ isLockedRand globalRand' ∗
    -- `emptyState = pb.HardState{}` (`node.go`), which `IsEmptyHardState` compares
    -- against; nothing but the initializer writes it
    "#emptyState" ∷ (globalAddr emptyState ↦□ (⟨W64 0, W64 0, W64 0⟩ : raftpb.HardState) : IProp GF) ∗
    -- the tables behind `IsLocalMsg` and `IsResponseMsg` (`util.go`), read by
    -- `RawNode.Step`; nothing but the initializer writes them, and their contents do
    -- not matter to the specs (2026-10-09)
    "#isLocalMsg" ∷ (globalAddr isLocalMsg ↦□ localMsgs : IProp GF) ∗
    "#isResponseMsg" ∷ (globalAddr isResponseMsg ↦□ responseMsgs : IProp GF) ∗
    -- the errors `RawNode.Step` returns for a message it does not step
    "#ErrStepLocalMsg" ∷ (globalAddr ErrStepLocalMsg ↦□ errStepLocal : IProp GF) ∗
    "#ErrStepPeerNotFound" ∷ (globalAddr ErrStepPeerNotFound ↦□ errStepPeer : IProp GF) ∗
    -- (2026-10-13) `errBreak = errors.New("break")`, the sentinel `hasUnappliedConfChanges`'
    -- callback stops `scan` with and then compares against (so `IsNewError`)
    "#ErrBreak" ∷ (∃ eb : GoInterface, (globalAddr errBreak ↦□ eb : IProp GF) ∗
      ⌜eb ≠ interface.nil ∧ IsNewError eb⌝))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  define_is_pkg_init isInitialized
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  build_get_is_pkg_init_wf

theorem isInitialized_access :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ⊢ isInitialized :=
  isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3

/-- `isLocalMsg[:]`, `isResponseMsg[:]`: the whole of a `[23]bool` as a slice, at any
fraction (Perennial's `slice_array` is for an owned array). -/
theorem array_slice_bool (l : Loc) (a : GoArray Bool 23) (dq : DFrac) :
    (typedPointsto l a dq : IProp GF) ⊢ slice.mk l (W64 23) (W64 23) ↦*{dq} a.arr := by
  obtain ⟨arr⟩ := a
  iintro H
  icases array_len _ _ _ _ $$ H with %Hn
  rw [ownSlice_unseal]; unfold ownSliceDef
  iright
  simp only
  rw [show sint.Z (W64 23) = (23 : Int) from rfl]
  iframe H
  ipureintro; omega

end init

end go_etcd_io.raft.v3

end Perennial
