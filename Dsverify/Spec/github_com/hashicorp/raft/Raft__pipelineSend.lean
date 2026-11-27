/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__pipelineSend.lean (241f27e).
-/
/-
`raft.Raft.pipelineSend`'s spec (replication subsystem, internal; stage 2).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

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

/-- `(*Raft).pipelineSend(s, p, nextIdx, lastIndex)` (stage 2, with the fork's fix `4dd03b4`: the
term check after building the request, as in `replicateTo`), by the replication goroutine of the
leader `i` of `T` for voter `j` in pipeline mode (`pipelineReplicate`): the request it sends on the
pipeline `p` of term `T` is valid (it was built from one version of the log: the term was still
`T` after every read); its local next index `*nextIdx` (owned) may move. -/
abbrev github_com.hashicorp.raft.Raft.pipelineSend.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc)
    (pI : GoInterfaceOk) (nxt : Loc) (lastIndex : w64) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s ∗ leaderIs γ T i ∗ termLb γ i T ∗ isPipeline pI γ j T ∗
     (∃ v : w64, nxt ↦ v) ∗ rtok tid }}
    (App (App (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"pipelineSend")) (Val #s))
      (Val #(GoInterface.ok pI))) (Val #nxt)) (Val #lastIndex))
  {{ (b : Bool), RET #b; rtok tid ∗ ∃ v : w64, nxt ↦ v }}

end spec

end Perennial
