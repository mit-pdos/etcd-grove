/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__requestVote.lean (241f27e).
-/
/-
`raft.(*Raft).requestVote`'s spec (internal to the RPC handlers): handles a valid RequestVote request (the protocol steps setTerm, grantVote) and responds.
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

/-- `(*Raft).requestVote(rpc, req)`: handles the valid request of candidate `c` for term `T` and
responds on `rpc.RespChan` (granted only with `voteIs γ i T c`). -/
abbrev github_com.hashicorp.raft.Raft.requestVote.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : RequestVoteRequest)
    (c : SID) (T li lt : Nat) (γc : ChanNames) (s : SState) (st : w32) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s st ∗ rtok tid ∗ p ↦ rq ∗ rvReq γ rq c T li lt ∗
     isChanBag (V := RPCResponse) γc rpc.RespChan'
       (rpcRespP RequestVoteResponse.ty
         (fun q => iprop(∃ rp : RequestVoteResponse, q ↦ rp ∗ rvResp γ rp i c T))) }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"requestVote")) (Val #rpc)) (Val #p))
  {{ RET #(); ∃ (s' : SState) (st' : w32), mainOwnAt r γ rc i s' st' ∗ rtok tid ∗
      ⌜st' = stFollower ∨ (st' = st ∧ s'.term = s.term ∧ s'.log = s.log)⌝ }}

end spec

end Perennial
