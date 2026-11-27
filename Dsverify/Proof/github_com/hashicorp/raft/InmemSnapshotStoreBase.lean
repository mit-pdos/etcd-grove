/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemSnapshotStoreBase.lean (241f27e).
-/
/-
Shared definitions of the `InmemSnapshotStore` proofs: the persistent handle on a store with no
snapshot. Nothing in scope creates a snapshot, so the embedded `RWMutex` guards
`hasSnapshot = false` forever; readers (`List`) borrow a reader token from a quarter thread pool with
their quarter token `rtok tid` (`HrVerify/Proof/Threads/QPool.lean`, D15).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.InmemStoreBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

/-- The namespace of the snapshot store's reader-token pool. -/
def snapPoolN : Namespace := nroot.@"inmemsnapshotstore"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The lock invariant: there is no snapshot. -/
def snapInv (m : Loc) (q : Qp) : IProp GF :=
  m.[InmemSnapshotStore, go!"hasSnapshot"] ↦{DFrac.own q} false

instance snapInv_fractional (m : Loc) : Fractional (snapInv (GF := GF) m) := by
  unfold snapInv; infer_instance

theorem snapInv_unfold (m : Loc) (q : Qp) :
    snapInv (GF := GF) m q ⊣⊢ m.[InmemSnapshotStore, go!"hasSnapshot"] ↦{DFrac.own q} false :=
  .rfl

/-- **The persistent handle on the `*InmemSnapshotStore` `m`** (no snapshot). -/
def isInmemSnapshotStore (m : Loc) : IProp GF :=
  iprop("#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
    "#Hpool" ∷ ∃ γp : GName, qpool.isQPool snapPoolN γp
      (sync.ownRWMutex (m.[InmemSnapshotStore, go!"RWMutex"]) (snapInv m)))

instance isInmemSnapshotStore_persistent m :
    Persistent (isInmemSnapshotStore (GF := GF) m) := by
  unfold isInmemSnapshotStore; infer_instance

end defs

end github_com.hashicorp.raft

end Perennial
