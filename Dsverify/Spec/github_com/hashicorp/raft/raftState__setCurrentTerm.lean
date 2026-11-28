/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__setCurrentTerm.lean (241f27e).
-/
/-
`raft.(*raftState).setCurrentTerm`'s spec (raft-internal interface, notes/raft-iface.md). The raw atomic store, called as `r.raftState.setCurrentTerm(t)` by `(*Raft).setCurrentTerm` (the receiver is the embedded `raftState`). The protocol step at the store (`setTerm_upd` or `electTerm_upd`) is the caller's ghost update `upd`, run with the cell's half of `termCouple` at the linearization point.
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

/-- `(*raftState).setCurrentTerm`: The raw atomic store, called as `r.raftState.setCurrentTerm(t)` by `(*Raft).setCurrentTerm` (the receiver is the embedded `raftState`). The protocol step at the store (`setTerm_upd` or `electTerm_upd`) is the caller's ghost update `upd`, run with the cell's half of `termCouple` at the linearization point. -/
abbrev github_com.hashicorp.raft.raftState.setCurrentTerm.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (t : w64) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ termCell r γ rc i ∗
     (∀ t0 : Nat, termV rc t0 -∗ |NC={⊤ \ ↑termN}=> termV rc (uint.nat t) ∗ Q) }}
    (App (Val ((r.[Raft, go!"raftState"]) @!! go.GoType.PointerType raftState.ty @!! go!"setCurrentTerm")) (Val #t))
  {{ RET #(); Q }}

end spec

end Perennial
