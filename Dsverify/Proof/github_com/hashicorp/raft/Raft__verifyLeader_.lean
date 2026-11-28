/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__verifyLeader_.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).verifyLeader` (stage 2; stage 4: over the leader's latest configuration,
fixes `6c3454c`, `4bb3955`, `0c7aa12`): the registration of a fresh verify future, or (a single voter,
the leader) its hand-off to the FSM goroutine.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__verifyLeader_
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__quorumSize
public import Dsverify.Spec.github_com.hashicorp.raft.asyncNotifyCh
public import Dsverify.Spec.github_com.hashicorp.raft.hasVote
public import Dsverify.Proof.github_com.hashicorp.raft.leader.VerifyCase
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hG sem package_sem hRB in
theorem nodup_getElem_not_mem_take' {α} {l : List α} {n : Nat} {x : α} (hnd : l.Nodup)
    (h : l[n]? = some x) : x ∉ l.take n := by
  intro hm
  have h1 : x ∈ l.drop n := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using h⟩
  rw [← List.take_append_drop n l, List.nodup_append] at hnd
  exact hnd.2.2 x hm x h1 rfl

/-- A select case receiving from a channel that is never sent on (`shutdownCh` in the main goroutine;
as `leaderLoop`'s). -/
theorem vl_dead_recv_clause {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Pos.Countable V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (ch : Loc) (γc : ChanNames) (h : Expr) (Ψ : val → IProp GF) :
    £ 1 ∗ £ 1 ∗ isChanBag (V := V) γc ch (fun _ => iprop(False)) ⊢
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) h) Ψ := by
  iintro ⟨Hl1, Hl2, #Hb⟩
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr; · ipureintro; rfl
  isplitr; · iapply is_bag_is_chan γc ch _ $$ Hb
  iapply bag_recv_au γc ch _ (fun v ok => iprop(WP (App h (Val (PairV #v #ok))) {{ Ψ }}))
    $$ [Hl1 Hl2] Hb
  · iframe
  inext; iintro %v Hf; iexfalso; iexact Hf

set_option maxHeartbeats 2000000 in
theorem github_com.hashicorp.raft.Raft.verifyLeader.wp_proof
    (wp_quorumSize : github_com.hashicorp.raft.Raft.quorumSize.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG))
    (wp_hasVote : github_com.hashicorp.raft.hasVote.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.verifyLeader.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
