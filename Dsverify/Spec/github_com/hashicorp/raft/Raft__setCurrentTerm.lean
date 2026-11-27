/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setCurrentTerm.lean (241f27e).
-/
/-
`raft.(*Raft).setCurrentTerm`'s spec (raft-internal interface, notes/raft-iface.md). Persists the term (stable store) and stores it in the `currentTerm` atomic, where the caller's protocol step (`setTerm_upd`/`electTerm_upd`) happens.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).setCurrentTerm`: Persists the term (stable store) and stores it in the `currentTerm` atomic, where the caller's protocol step (`setTerm_upd`/`electTerm_upd`) happens. -/
abbrev github_com.hashicorp.raft.Raft.setCurrentTerm.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (sst : StableAbs) (t : w64) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ rc.ownS sst ∗
     (∀ t0 : Nat, termCouple γ i t0 ={⊤ \ ↑termN}=∗ termCouple γ i (uint.nat t) ∗ Q) }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setCurrentTerm")) (Val #t))
  {{ RET #(); rc.ownS { sst with ints := sst.ints.insert (go!"CurrentTerm" : List w8) t } ∗ Q }}

end spec

end Perennial
