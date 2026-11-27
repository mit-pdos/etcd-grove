/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__LeadershipTransferToServer.lean (241f27e).
-/
/-
`raft.(*Raft).LeadershipTransferToServer`'s spec (client-facing, stage 2; notes/stage2-plan.md D6).
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

/-- `(*Raft).LeadershipTransferToServer(id, address)` (stage 2) to a voter `j` given as both its id
and address (hr3: `inproc.Addr(t)`): as `LeadershipTransfer`, a future whose `Error()` may be called
once (any answer).
Why it is true of the code: `initiateLeadershipTransfer(&id, &address)` answers an error itself
when `j = i`, else sends the future with target `j` (`ltfP`: a voter as `ID` and `Address`, which
the leader's `TimeoutNow` call needs) or returns `errorFuture{ErrEnqueueTimeout}`. -/
abbrev github_com.hashicorp.raft.Raft.LeadershipTransferToServer.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i j : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ isSrv γ j }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"LeadershipTransferToServer"))
      (Val #(j : GoString))) (Val #(j : GoString)))
  {{ (fi : GoInterface), RET #fi; futWait fi (fun _ => iprop(True)) }}

end spec

end Perennial
