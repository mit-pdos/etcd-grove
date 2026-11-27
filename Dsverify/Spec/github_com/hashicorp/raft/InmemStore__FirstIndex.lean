/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__FirstIndex.lean (241f27e).
-/
/-
`raft.(*InmemStore).FirstIndex`'s spec: returns some index and `nil` (the read lock paid for by
the thread's `rtok`). As `isLogStore`'s `FirstIndex`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.InmemStoreBase

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

open github_com.hashicorp.raft proto in
/-- `i.FirstIndex()` returns some index and `nil`. -/
abbrev github_com.hashicorp.raft.InmemStore.FirstIndex.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (tid : Nat),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      rtok tid) -∗
    (∀ r : w64, rtok tid -∗ Φ (PairV #r #interface.nil)) -∗
    WP (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"FirstIndex")) (Val #()))
      {{ Φ }}

end spec

end Perennial
