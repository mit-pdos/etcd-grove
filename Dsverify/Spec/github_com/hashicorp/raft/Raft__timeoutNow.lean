/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__timeoutNow.lean (241f27e).
-/
/-
`raft.(*Raft).timeoutNow`'s spec (internal to the RPC handlers, `processRPC`): a TimeoutNow request
(leadership transfer, stage 2) makes the server a candidate (`setState(Candidate)`, the flag
`candidateFromLeadershipTransfer` set) and is answered; no protocol state changes.
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

/-- `(*Raft).timeoutNow`: the main goroutine becomes a candidate of the same protocol state and
answers the request. -/
abbrev github_com.hashicorp.raft.Raft.timeoutNow.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : TimeoutNowRequest)
    (γc : ChanNames) (s : SState) (st : w32) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s st ∗ rtok tid ∗ p ↦ rq ∗
     isChanBag (V := RPCResponse) γc rpc.RespChan'
       (rpcRespOkP TimeoutNowResponse.ty (fun q => iprop(∃ rp : TimeoutNowResponse, q ↦ rp ∗
         ∃ id ad : List w8, rp.RPCHeader'.ID' ↦*□ id ∗ rp.RPCHeader'.Addr' ↦*□ ad))) }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"timeoutNow")) (Val #rpc)) (Val #p))
  {{ RET #(); mainOwnAt r γ rc i s stCandidate ∗ rtok tid }}

end spec

end Perennial
