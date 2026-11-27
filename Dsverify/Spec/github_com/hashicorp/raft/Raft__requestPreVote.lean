/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__requestPreVote.lean (241f27e).
-/
/-
`raft.(*Raft).requestPreVote`'s spec (internal to the RPC handlers): answers a pre-vote request (no protocol step).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net

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

/-- `(*Raft).requestPreVote(rpc, req)`: answers the pre-vote request of term `T` on
`rpc.RespChan`. -/
abbrev github_com.hashicorp.raft.Raft.requestPreVote.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : RequestPreVoteRequest)
    (c : SID) (T : Nat) (γc : ChanNames) (s : SState) (st : w32) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s st ∗ rtok tid ∗ p ↦ rq ∗ pvReq rq c T ∗
     isChanBag (V := RPCResponse) γc rpc.RespChan'
       (rpcRespP RequestPreVoteResponse.ty
         (fun q => iprop(∃ rp : RequestPreVoteResponse, q ↦ rp ∗ pvResp γ rp T))) }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"requestPreVote")) (Val #rpc)) (Val #p))
  {{ RET #(); ∃ (s' : SState) (st' : w32), mainOwnAt r γ rc i s' st' ∗ rtok tid ∗
      ⌜st' = stFollower ∨ (st' = st ∧ s'.term = s.term ∧ s'.log = s.log)⌝ }}

end spec

end Perennial
