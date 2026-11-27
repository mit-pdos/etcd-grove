/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__ApplyLog.lean (241f27e).
-/
/-
`raft.(*Raft).ApplyLog`'s spec (API-internal): as `Apply`.
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

/-- `(*Raft).ApplyLog` (API-internal; called by `Apply`): the client's command (data `d`, with its
operation token, and the log's read-only extensions) is sent on `applyCh` as a fresh future, or the enqueue times out. -/
abbrev github_com.hashicorp.raft.Raft.ApplyLog.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (lv : Log) (d : List w8) (n : Nat)
    (tmo : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ lv.Data' ↦*□ d ∗
      (∃ x : List w8, lv.Extensions' ↦*□ x) ∗ opTok γ d n }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"ApplyLog")) (Val #lv)) (Val #tmo))
  {{ (fi : GoInterface), RET #fi; futureOwn γ rc fi d n }}

end spec

end Perennial
