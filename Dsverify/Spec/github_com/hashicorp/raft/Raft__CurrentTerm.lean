/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__CurrentTerm.lean (241f27e).
-/
/-
`raft.(*Raft).CurrentTerm`'s spec (raft-internal interface, notes/raft-iface.md). Strong form: with the server's protocol state (an observer's filter at `setState(Leader)`), its term; weak form: some term.
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

/-- `(*Raft).CurrentTerm`: Strong form: with the server's protocol state (an observer's filter at
`setState(Leader)`), its term. Witness form (stage 2; it replaces stage 1's weak form "some term"):
for a caller holding a snapshot `s0` (`histLb`), the term `t` it returns was `i`'s term at a
snapshot after `s0` (the `currentTerm` atomic load, `getCurrentTerm`, with `gprot.termCouple_now`
inside the cell's invariant). hr3's `readAt` reads the term around `Barrier` and `VerifyLeader`
and so learns that their term is the one it read. -/
abbrev github_com.hashicorp.raft.Raft.CurrentTerm.spec : Prop :=
  (∀ (r : Loc) (γ : GNames) (i : SID) (s : SState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ Inv γ ∗ termCell r γ i ∗ srvOwn γ i s }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"CurrentTerm")) (Val #()))
  {{ RET #(W64 s.term); srvOwn γ i s }}) ∧
  (∀ (r : Loc) (γ : GNames) (i : SID) (s0 : Snap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ Inv γ ∗ isSrv γ i ∗
     termCell r γ i ∗ histLb γ s0 }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"CurrentTerm")) (Val #()))
  {{ (t : w64), RET #t; ∃ s' : Snap, histLb γ s' ∗ ⌜snapLe s0 s' ∧ s'.term i = uint.nat t⌝ }})

end spec

end Perennial
