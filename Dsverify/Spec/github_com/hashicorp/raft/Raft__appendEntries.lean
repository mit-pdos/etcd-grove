/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__appendEntries.lean (241f27e).
-/
/-
`raft.(*Raft).appendEntries`'s spec (internal to the RPC handlers): handles a valid AppendEntries request (the protocol steps truncate, followerStore, ack, learnCommit, setCidx) and responds.
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

/-- `(*Raft).appendEntries(rpc, a)`: handles the valid request `a` of term `T` and responds on
`rpc.RespChan` (success only with `ackIs γ i T (prev + |ents|)`). (Stage 2) A candidate from a leadership transfer
(`candidateFromLeadershipTransfer`) does not step down on a valid request of its term: it may stay
Candidate and store entries; the request's leader `ℓ ≠ i` then leads its term. -/
abbrev github_com.hashicorp.raft.Raft.appendEntries.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : AppendEntriesRequest)
    (snd : SID) (T prev pt : Nat) (ents : RLog) (lci : Nat) (ss : Snap) (γc : ChanNames) (s : SState) (st : w32) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s st ∗ rtok tid ∗ p ↦ rq ∗ aeReq γ rq snd T prev pt ents lci ss ∗
     isChanBag (V := RPCResponse) γc rpc.RespChan'
       (rpcRespP AppendEntriesResponse.ty
         (fun q => iprop(∃ rp : AppendEntriesResponse, q ↦ rp ∗ aeResp γ rp i T (prev + ents.length) (isHb prev ents lci) ss))) }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"appendEntries")) (Val #rpc)) (Val #p))
  {{ RET #(); ∃ (s' : SState) (st' : w32), mainOwnAt r γ rc i s' st' ∗ rtok tid ∗
      (⌜st' = stFollower ∨ (st' = st ∧ s'.term = s.term ∧ s'.log = s.log)⌝ ∨
       ⌜st' = st ∧ st = stCandidate ∧ s'.term = s.term⌝ ∗ ∃ ℓ : SID, ⌜ℓ ≠ i⌝ ∗ leaderIs γ s.term ℓ) }}

end spec

end Perennial
