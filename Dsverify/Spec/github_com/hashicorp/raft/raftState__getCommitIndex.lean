/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__getCommitIndex.lean (241f27e).
-/
/-
`raft.(*raftState).getCommitIndex`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). Strong form: the main goroutine reads its `cidx`; weak form (the replication goroutine of the leader of `T`, `readCidx_repl`): a commit index that may be sent in `T`, or the server already left `T`.
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

/-- `(*raftState).getCommitIndex`: Called through `*Raft` (promoted). Strong form: the main goroutine reads its `cidx`; weak form (the replication goroutine of the leader of `T`, `readCidx_repl`): a commit index that may be sent in `T`, or the server already left `T`. -/
abbrev github_com.hashicorp.raft.raftState.getCommitIndex.spec : Prop :=
  (∀ (r : Loc) (γ : GNames) (i : SID) (s : SState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ Inv γ ∗ cidxCell r γ i ∗ srvOwn γ i s }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getCommitIndex")) (Val #()))
  {{ RET #(W64 s.cidx); srvOwn γ i s }}) ∧
  (∀ (r : Loc) (γ : GNames) (i : SID) (T : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ Inv γ ∗ cidxCell r γ i ∗ leaderIs γ T i ∗ termLb γ i T }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getCommitIndex")) (Val #()))
  {{ (c : w64), RET #c; lciOk γ T (uint.nat c) ∨ termLb γ i (T + 1) }})

end spec

end Perennial
