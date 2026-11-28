/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__StoreLog.lean (241f27e).
-/
/-
`raft.(*InmemStore).StoreLog`'s spec: `StoreLogs` of one entry, logically atomic. As
`isLogStore`'s `StoreLog` (without the durable-prefix premise).
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
/-- `i.StoreLog(l)` inserts the entry `e` at index `first`, atomically (stage 3: partial map). -/
abbrev github_com.hashicorp.raft.InmemStore.StoreLog.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (p : Loc) (first : Nat) (e : Entry),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      ⌜first < 2 ^ 64⌝ ∗ logPtr p first e) -∗
    (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, inmemLogs γs A ∗
      (inmemLogs γs (A.store first [e]) ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
    WP (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"StoreLog")) (Val #p))
      {{ Φ }}

end spec

end Perennial
