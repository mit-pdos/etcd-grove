/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__pipelineReplicate.lean (241f27e).
-/
/-
`raft.(*Raft).pipelineReplicate`'s spec (replication subsystem, internal).
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

/-- `(*Raft).pipelineReplicate` (stage 2), by the replication goroutine of the leader `i` of `T`
to `j` (the resources of `replicateTo`): makes a pipeline of term `T`
(`AppendEntriesPipeline`; its error, a raft error value, is returned as it is: REPL-5), starts the decoder (`pipelineDecode`,
through `goFunc`), sends with `pipelineSend` until the decoder stops, the stop channel fires, or a
send fails, then stops the decoder and returns `nil`. The stop channel is a close-only broadcast
channel (`stopChan`): its receivers keep receiving after the close. -/
abbrev github_com.hashicorp.raft.Raft.pipelineReplicate.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc)
    (γs : StopNames) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s ∗ leaderIs γ T i ∗ termLb γ i T ∗ replStopCh s γs ∗
     replFields s ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"pipelineReplicate")) (Val #s))
  {{ (err : GoInterface), RET #err; rtok tid ∗ replFields s ∗
      (⌜err = interface.nil⌝ ∨ errOk err ∗ ∃ c, isRaftErr c err) }}

end spec

end Perennial
