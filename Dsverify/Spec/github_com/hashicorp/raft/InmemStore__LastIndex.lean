/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__LastIndex.lean (241f27e).
-/
/-
`raft.(*InmemStore).LastIndex`'s spec: logically atomic read of the number of entries (the
read lock paid for by the thread's `rtok`). As `isLogStore`'s `LastIndex`.
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
/-- `i.LastIndex()` returns the last index written (`hi`) and `nil`, atomically. -/
abbrev github_com.hashicorp.raft.InmemStore.LastIndex.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (tid : Nat),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      rtok tid) -∗
    (|={⊤,∅}=> ▷ ∃ A, inmemLogs γs A ∗
      (inmemLogs γs A ={∅,⊤}=∗ (rtok tid -∗ Φ (PairV #A.hi #interface.nil)))) -∗
    WP (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"LastIndex")) (Val #()))
      {{ Φ }}

end spec

end Perennial
