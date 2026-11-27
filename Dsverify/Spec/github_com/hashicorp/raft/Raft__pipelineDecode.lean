/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__pipelineDecode.lean (241f27e).
-/
/-
`raft.Raft.pipelineDecode`'s spec (replication subsystem, internal; stage 2).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplPipe

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

/-- `(*Raft).pipelineDecode(s, p, stopCh, finishCh)` (stage 2), the decoder goroutine of the
pipeline `p` of term `T` to `j` (started by `pipelineReplicate` through `goFunc`): each response's
facts are about its own request (`pipeFut`, of term `T`), so a success acknowledges in `T`
(`updateLastAppended`, with the writer's half of `nextIndex`, lent by `pipelineReplicate`); it
stops on a newer term, a failure or the close of `stopCh` (an SPSC channel closed by
`pipelineReplicate`), and closes `finishCh` giving the half back. -/
abbrev github_com.hashicorp.raft.Raft.pipelineDecode.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc)
    (pI : GoInterfaceOk) (stopCh finCh : Loc) (γst : SpscNames) (γf : FinNames) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s ∗ isPipeline pI γ j T ∗
     hbStop γst stopCh ∗ spscConsumer γst ([] : List Unit) ∗
     finChan γf finCh (nextHalf s) ∗ finCloser γf ∗ nextHalf s ∗ rtok tid }}
    (App (App (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"pipelineDecode")) (Val #s))
      (Val #(GoInterface.ok pI))) (Val #stopCh)) (Val #finCh))
  {{ RET #(); rtok tid }}

end spec

end Perennial
