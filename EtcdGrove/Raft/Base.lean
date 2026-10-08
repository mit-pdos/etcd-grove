/-
Port of etcd-grove's `new/proof/go_etcd_io/raft/v3_proof/base.v`: package
initialization instances for `go.etcd.io/raft/v3` and the packages it imports.

This replaces Perennial's `Perennial.Proof.go_etcd_io.raft.v3_proof.base` (the port of
upstream's `base.v`), which must not be imported alongside it: `IsPkgInit` has one
instance per package, and etcd-grove's raft and `crypto/rand` instances are stronger.
Everything here is an assumption about package initialization: nothing proves it from
the packages' `initialize'` functions.

Lean notes: see Perennial's `base.lean` for the instances that live in other Perennial
files (`strings`, `math`, `bytes`, `log`, `io`, `errors`).
-/
import EtcdGrove.Code.go_etcd_io.raft.v3
import EtcdGrove.GeneratedProof.go_etcd_io.raft.v3
import EtcdGrove.GeneratedProof.go_etcd_io.raft.v3.raftpb
import Perennial.Proof.ProofPrelude
import Perennial.Proof.context
import Perennial.Proof.sync
import Perennial.Proof.fmt
import Perennial.Proof.slices_proof.slices_init
import Perennial.Proof.cmp
import Perennial.Proof.encoding.binary
import Perennial.Proof.strings
import Perennial.Proof.math
import Perennial.Proof.bytes
import Perennial.Proof.log
import Perennial.Proof.io
import Perennial.Proof.errors
import Perennial.Proof.sync_proof.mutex

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

instance big_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.math.big :=
  define_is_pkg_init iprop(True)
instance big_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.big :=
  build_get_is_pkg_init_wf

/-- `crypto/rand`'s package-level `Reader` (an `io.Reader`). `lockedRand.Intn` reads it
through `GlobalVarAddr` to pass it to `rand.Int`, so a proof of that method needs the
points-to. Its value is opaque: nothing is known about it beyond being the reader the
package installed, and the `rand.Int` triple is stated for exactly that reader. -/
def isRandInitialized : IProp GF :=
  iprop(∃ rdr : GoInterface,
    "#Reader" ∷ (globalAddr crypto.rand.Reader ↦□ rdr : IProp GF))

instance rand_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.crypto.rand :=
  define_is_pkg_init isRandInitialized
instance rand_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.rand :=
  build_get_is_pkg_init_wf

instance os_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.os :=
  define_is_pkg_init iprop(True)
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
      (globalRand' : Loc),
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
    "#emptyState" ∷ (globalAddr emptyState ↦□ (⟨W64 0, W64 0, W64 0⟩ : raftpb.HardState) : IProp GF))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  define_is_pkg_init isInitialized
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  build_get_is_pkg_init_wf

theorem isRandInitialized_access :
    isPkgInit (PROP := IProp GF) pkg_id.crypto.rand ⊢ isRandInitialized :=
  isPkgInit_access (PROP := IProp GF) pkg_id.crypto.rand

theorem isInitialized_access :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ⊢ isInitialized :=
  isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3

end init

end go_etcd_io.raft.v3

end Perennial
