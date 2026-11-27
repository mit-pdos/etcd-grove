/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemSnapshotStore__List.lean (241f27e).
-/
/-
`raft.(*InmemSnapshotStore).List`'s spec: there is no snapshot, so `List` returns an empty
slice and `nil`. Its read lock is paid for by the calling thread's `rtok`, given back.
(`isSnapshotStore`'s `List` lacks the `rtok`: see the report.)
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.InmemSnapshotStoreBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft in
/-- `m.List()` returns an empty slice and `nil`. -/
abbrev github_com.hashicorp.raft.InmemSnapshotStore.List.spec : Prop :=
  ∀ (m : Loc) (tid : Nat),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemSnapshotStore m ∗
      rtok tid) -∗
    (∀ s : GoSlice, s ↦* ([] : List Loc) -∗ rtok tid -∗ Φ (PairV #s #interface.nil)) -∗
    WP (App (Val (m @!! go.GoType.PointerType InmemSnapshotStore.ty @!! go!"List")) (Val #()))
      {{ Φ }}

end spec

end Perennial
