/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__getCurrentTerm.lean (241f27e).
-/
/-
`raft.(*raftState).getCurrentTerm`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). Strong form: the main goroutine, with its protocol state, reads its term; weak form (any goroutine): a term at least any lower bound it knows, and a lower bound for the term read (the replication goroutine's final term check uses it to refute `termLb γ i (T+1)`).
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

/-- `(*raftState).getCurrentTerm`: Called through `*Raft` (promoted). Strong form: the main goroutine, with its protocol state, reads its term; weak form (any goroutine): a term at least any lower bound it knows, and a lower bound for the term read (the replication goroutine's final term check uses it to refute `termLb γ i (T+1)`). -/
abbrev github_com.hashicorp.raft.raftState.getCurrentTerm.spec : Prop :=
  (∀ (r : Loc) (γ : GNames) (i : SID) (s : SState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ Inv γ ∗ termCell r γ i ∗ srvOwn γ i s }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getCurrentTerm")) (Val #()))
  {{ RET #(W64 s.term); srvOwn γ i s }}) ∧
  (∀ (r : Loc) (γ : GNames) (i : SID) (t0 : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ termCell r γ i ∗ termLb γ i t0 }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getCurrentTerm")) (Val #()))
  {{ (t : w64), RET #t; termLb γ i (uint.nat t) ∗ ⌜t0 ≤ uint.nat t⌝ }})

end spec

end Perennial
