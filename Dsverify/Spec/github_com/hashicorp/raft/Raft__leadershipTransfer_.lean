/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__leadershipTransfer_.lean (241f27e).
-/
/-
`raft.(*Raft).leadershipTransfer`'s spec (the leadership transfer goroutine, MAIN-L, stage 2).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Defs
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

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

/-- `(*Raft).leadershipTransfer(id, address, repl, stopCh, doneCh)` (the goroutine the leader loop
starts for a leadership transfer to the voter `j`, `address = j`, whose replication goroutine is
`repl`): until the follower has the leader's last index, it asks the replication goroutine to
replicate (a `*deferError` on `triggerDeferErrorCh`) and waits for its answer or the stop channel
(a broadcast channel closed by the transfer's other goroutine); then sends `TimeoutNow` to `j`
through the transport (with its thread token); it ends by sending one error on `doneCh` (any
value). -/
abbrev github_com.hashicorp.raft.Raft.leadershipTransfer.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (id : ServerID)
    (repl stopCh doneCh : Loc) (γst γd : ChanNames) (Pst : IProp GF) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j repl ∗ ownBroadcastChan stopCh γst Pst .Unknown ∗
     isChanBag (V := GoInterface) γd doneCh (fun _ => iprop(True)) ∗ rtok tid }}
    (App (App (App (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"leadershipTransfer"))
      (Val #id)) (Val #(j : ServerAddress))) (Val #repl)) (Val #stopCh)) (Val #doneCh))
  {{ RET #(); rtok tid }}

end spec

end Perennial
