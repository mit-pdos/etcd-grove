/-
(p-link, HANDLERS-5) Every message a delivery's step sends or broadcasts is encodable (`OutsWf`):
command values shorter than `2 ^ 16` (the ops' commands, `opsPre`), command lists shorter than
`2 ^ 62` (a no-op or an instance's batch, `InvX`), deps of `N` entries.

The sent messages of the reply handlers are read off the post-state's messages (`Inv` of the
post-state: a PreAccept/Accept/Commit carries a Phase 1's / Accept's / commit's value, which is a
no-op or its instance's batch); `handlePrepare`'s and `handlePreAccept`'s replies are read off
the pre-state's record (`NR` for a NONE record).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostDeliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model model.NoneRec

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem lk_slots {S : Sys} (h : Inv S) : Inv.slots S := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h.1; exact h

theorem lk_commitMsgs {S : Sys} (h : Inv S) : Inv.commitMsgs S := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h.1; exact h

theorem lk_ballotOwner {S : Sys} (h : Inv S) : Inv.ballotOwner S := by
  obtain ⟨-, -, -, -, -, h, -⟩ := h.1; exact h

/-- A command list that is a no-op or an instance's batch. -/
def goodCmds (S : Sys) (cs : List WCmd) : Prop :=
  cs = noop ∨ ∃ x ps, S.owner x = some ps ∧ cs = ps.map (·.cmd)

theorem cmdsWf_of_good [GooseExts] [GoGlobalContext] {S : Sys} (hS : Inv S) (hX : InvX S) (hops : opsPre S)
    {cs : List WCmd} (h : goodCmds S cs) : cmdsWf cs := by
  rcases h with rfl | ⟨x, ps, hx, rfl⟩
  · refine ⟨by simp [noop], fun c hc => ?_⟩
    simp only [noop, List.mem_singleton] at hc; subst hc; simp [cmdWf]
  · refine ⟨by simpa using hX.2 x ps hx, fun c hc => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hmem := (lk_slots hS).2 x ps hx p hp
    obtain ⟨inp, hpre, hc⟩ := hops _ hmem
    simp only at hc
    rw [cmdWf, hc]
    cases inp with
    | get k => simp [cmdOf]
    | put k v => simp only [cmdOf]; have := hpre.2.2; omega
    | scan k n => simp only [cmdOf, u64Le_length]; decide

theorem depsWf_of_ok {ds : List w32} (h : depsOk ds) : depsWf ds := by
  unfold depsWf; rw [h.1]; unfold nR; decide

theorem valOk_good {S : Sys} (hS : Inv S) {r : Nat} {x : InstId} {b : w32} {v : model.Val}
    (h : S.ev r (.phase1 x b v) ∨ S.ev r (.accept x b v)) : goodCmds S v.cmds := by
  rcases hS.2.valOk r x b v h with h' | ⟨ps, hps, h'⟩
  · exact Or.inl h'
  · exact Or.inr ⟨x, ps, hps, h'⟩

theorem committed_good {S : Sys} (hS : Inv S) {x : InstId} {v : model.Val} (h : S.committedVal x v) :
    goodCmds S v.cmds := by
  rcases (lk_slots hS).1 x v h with h' | ⟨ps, hps, h'⟩
  · exact Or.inl h'
  · exact Or.inr ⟨x, ps, hps, h'⟩

/-- A message of the system other than a PrepareReply or a PreAcceptReply is encodable. -/
theorem msg_wf [GooseExts] [GoGlobalContext] {S : Sys} (hS : Inv S) (hX : InvX S) (hops : opsPre S)
    {fr to : Nat} {m : Msg} (hm : m ∈ S.msgs fr to)
    (hk1 : ∀ p, m ≠ .prepareReply p) (hk2 : ∀ p, m ≠ .preAcceptReply p) : m.wf := by
  have hdeps := (hS.1.2.1 fr to m hm).2
  cases m with
  | prepareReply p => exact absurd rfl (hk1 p)
  | preAcceptReply p => exact absurd rfl (hk2 p)
  | preAccept p =>
    have hev := ((lk_ballotOwner hS).2.2.2.2.1 fr to p hm).2
    exact ⟨cmdsWf_of_good hS hX hops (valOk_good hS (Or.inl hev)),
      depsWf_of_ok (hdeps _ (by simp [Msg.depsFields]))⟩
  | accept p =>
    have hev := ((lk_ballotOwner hS).2.2.2.2.2 fr to p hm).2
    exact ⟨cmdsWf_of_good hS hX hops (valOk_good hS (Or.inr hev)),
      depsWf_of_ok (hdeps _ (by simp [Msg.depsFields]))⟩
  | commit p =>
    obtain ⟨r, b, hev⟩ := lk_commitMsgs hS fr to p hm
    exact ⟨cmdsWf_of_good hS hX hops (committed_good hS (Or.inl ⟨r, b, hev⟩)),
      depsWf_of_ok (hdeps _ (by simp [Msg.depsFields]))⟩
  | tryPreAccept p => exact absurd rfl ((hS.1.2.2.2.1 fr to _ hm).1 p)
  | prepare p => trivial
  | acceptReply p => trivial
  | tryPreAcceptReply p => trivial
  | beacon _ => trivial
  | beaconReply _ => trivial

end Perennial.github_com.imdea_software.swiftpaxos_epaxos

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model model.NoneRec

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The reply handlers' outputs: their sends are not replies of the two read-off kinds, and a
broadcast is the last output, with a peer and a send to make -/

def GoodO (outs : List Out) : Prop :=
  (∀ t m', Out.send t m' ∈ outs → (∀ p, m' ≠ .prepareReply p) ∧ (∀ p, m' ≠ .preAcceptReply p)) ∧
  ∀ b, Out.bcast b ∈ outs → outs.getLast? = some (.bcast b) ∧ b.sent < b.need ∧ b.peers ≠ []

theorem GoodO_ite {c : Prop} [Decidable c] {a b : RState × List Out} (ha : c → GoodO a.2)
    (hb : ¬c → GoodO b.2) : GoodO (if c then a else b).2 := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem GoodO_nil : GoodO [] := ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

theorem GoodO_evs (evs : List Out) (h : ∀ o ∈ evs, ∃ e, o = .ev e) : GoodO evs := by
  refine ⟨fun t m' hm => ?_, fun b hb => ?_⟩
  · obtain ⟨e, he⟩ := h _ hm; cases he
  · obtain ⟨e, he⟩ := h _ hb; cases he

theorem GoodO_leaf (evs : List Out) (b : Bcast) (h : ∀ o ∈ evs, ∃ e, o = .ev e)
    (hs : b.sent < b.need) (hp : b.peers ≠ []) : GoodO (evs ++ [.bcast b]) := by
  refine ⟨fun t m' hm => ?_, fun b' hb => ?_⟩
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, he⟩ := h _ hm; cases he
    · simp at hm
  · rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨e, he⟩ := h _ hb; cases he
    · simp only [List.mem_singleton, Out.bcast.injEq] at hb; subst hb
      exact ⟨by simp, hs, hp⟩

@[simp] theorem updateConflicts_peerOrder (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) :
    (updateConflicts σ cmds q n seq).peerOrder = σ.peerOrder := by
  unfold updateConflicts
  generalize σ = τ
  induction cmds generalizing τ with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl_cons]; rw [ih]

@[simp] theorem bumpRecvBallot_peerOrder (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).peerOrder = σ.peerOrder := by
  unfold bumpRecvBallot; split <;> rfl

theorem take_ne_nil {l : List Nat} (h : l ≠ []) : l.take (nR - 1) ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => simp [nR]

theorem startPhase1_good {σ : RState} (hpo : σ.peerOrder ≠ []) (cmds : List WCmd) (x : InstId)
    (replica n ballot : w32) (ps : Option (List Proposal)) :
    GoodO (startPhase1 σ cmds x replica n ballot ps).2 := by
  unfold startPhase1
  dsimp only
  apply GoodO_leaf [_, _, _]
  · intro o ho; simp at ho; rcases ho with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · simp [bcastPreAcceptOf, fR]
  · simp only [bcastPreAcceptOf]
    apply take_ne_nil
    split <;> simpa [RState.setInst] using hpo

theorem nackBranch_good {σ : RState} (x : InstId) (inst : InstRec) (lb : LbRec) :
    GoodO (nackBranch σ x inst lb).2 := by
  unfold nackBranch
  dsimp only
  apply GoodO_ite
  · intro _
    apply GoodO_leaf
    · intro o ho
      split at ho
      · simp at ho; subst ho; exact ⟨_, rfl⟩
      · simp at ho
    · simp [bcastPrepareOf, nR]
    · simp [bcastPrepareOf, cyclePeers, nR]
  · intro _; exact GoodO_nil

set_option hygiene false in
macro "good_close" : tactic => `(tactic| first
  | exact GoodO_nil
  | exact nackBranch_good _ _ _
  | (dsimp only
     apply GoodO_leaf
     · intro o ho
       split at ho
       · simp at ho; subst ho; exact ⟨_, rfl⟩
       · simp at ho
     · simp [bcastPrepareOf, nR]
     · simp [bcastPrepareOf, cyclePeers, nR])
  | exact startPhase1_good (by simpa [RState.setInst] using hpo) _ _ _ _ _ _
  | (apply GoodO_evs; intro o ho; simp at ho; rcases ho with rfl | rfl <;> exact ⟨_, rfl⟩)
  | (apply GoodO_evs; intro o ho; simp at ho; subst ho; exact ⟨_, rfl⟩)
  | (apply GoodO_leaf [_, _]
     · intro o ho; simp at ho; rcases ho with rfl | rfl <;> exact ⟨_, rfl⟩
     · simp [bcastAcceptOf, bcastCommitOf, nR]
     · simp only [bcastAcceptOf, bcastCommitOf]; apply take_ne_nil
       simpa [RState.setInst, updateCommitted] using hpo)
  | (apply GoodO_leaf [_]
     · intro o ho; simp at ho; subst ho; exact ⟨_, rfl⟩
     · simp [bcastAcceptOf, bcastCommitOf, nR]
     · simp only [bcastAcceptOf, bcastCommitOf]; apply take_ne_nil
       simpa [RState.setInst, updateCommitted] using hpo))

theorem hPrepareReply_good {σ : RState} (hpo : σ.peerOrder ≠ []) (m : PrepareReply) :
    GoodO (hPrepareReply σ m).2 := by
  unfold hPrepareReply
  dsimp only
  split
  · exact GoodO_nil
  split
  · exact GoodO_nil
  repeat' (apply GoodO_ite <;> intro _)
  all_goals good_close

theorem hPreAcceptReply_good {σ : RState} (hpo : σ.peerOrder ≠ []) (m : PreAcceptReply) :
    GoodO (hPreAcceptReply σ m).2 := by
  unfold hPreAcceptReply
  dsimp only
  split
  · exact GoodO_nil
  split
  · exact GoodO_nil
  repeat' (apply GoodO_ite <;> intro _)
  all_goals good_close

theorem hAcceptReply_good {σ : RState} (hpo : σ.peerOrder ≠ []) (m : AcceptReply) :
    GoodO (hAcceptReply σ m).2 := by
  unfold hAcceptReply
  dsimp only
  split
  · exact GoodO_nil
  split
  · exact GoodO_nil
  repeat' (apply GoodO_ite <;> intro _)
  all_goals good_close

/-! ## A step's outputs in the post-state's messages -/

theorem pendFold_last (init : List Out) (b : Bcast) (p : Option Bcast) :
    pendFold (init ++ [.bcast b]) p = b.norm := by
  unfold pendFold; rw [List.foldl_append]; rfl

theorem applyStep_outs_msgs (S : Sys) (i : Nat) (r : RState × List Out) (hidle : S.pending i = none) :
    (∀ t m', Out.send t m' ∈ r.2 → m' ∈ (S.applyStep i r).msgs i t) ∧
    (∀ b, Out.bcast b ∈ r.2 → r.2.getLast? = some (.bcast b) → b.sent < b.need → b.peers ≠ [] →
      (S.applyStep i r).pending i = some b ∧ ∃ p, b.m ∈ (S.applyStep i r).msgs i p) := by
  constructor
  · intro t m' hm
    unfold Sys.msgs Sys.applyStep
    apply List.mem_append_left; apply List.mem_append_right
    rw [Sys.foldl_emit_outbox]
    simp only [if_true]
    apply List.mem_append_right
    exact List.mem_filterMap.mpr ⟨_, hm, by simp [Out.sendTo]⟩
  · intro b hb hl hs hp
    obtain ⟨p, ps, hps⟩ : ∃ p ps, b.peers = p :: ps := by
      cases h : b.peers with
      | nil => exact absurd h hp
      | cons p ps => exact ⟨p, ps, rfl⟩
    obtain ⟨ys, hsplit⟩ := List.getLast?_eq_some_iff.mp hl
    have hpend : (S.applyStep i r).pending i = some b := by
      unfold Sys.applyStep
      rw [Sys.foldl_emit_pending, if_pos rfl, hsplit, pendFold_last]
      unfold Bcast.norm; rw [if_neg (by rw [hps]; simp; omega)]
    refine ⟨hpend, p, ?_⟩
    unfold Sys.msgs Sys.intended
    apply List.mem_append_right
    rw [hpend]; simp [hps]

theorem hPreAccept_sends (σ : RState) (m : PreAccept) :
    ∀ t m', Out.send t m' ∈ (hPreAccept σ m).2 →
      ∃ r : PreAcceptReply, m' = .preAcceptReply r ∧ r.committedDeps.length = nR := by
  intro t m' h
  unfold hPreAccept at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (rcases List.mem_append.mp h with h | h
       · simp at h
       · simp only [List.mem_singleton, Out.send.injEq] at h
         obtain ⟨-, rfl⟩ := h
         exact ⟨_, rfl, by simp [RState.committedList]⟩)

theorem lk_votes {S : Sys} (h : Inv S) : Inv.votesFollowProposals S := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := h.1; exact h

theorem lk_agreement {S : Sys} (h : Inv S) : Inv.agreement S := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h.1; exact h

/-- A record past NONE holds a no-op or its instance's batch. -/
theorem rec_good {S : Sys} (hS : Inv S) {i : Nat} (hi : i < nR) {x : InstId} {w : InstRec}
    (hw : (S.rep i).inst x = some w) (hst : w.status ≠ stNONE) {cs : List WCmd}
    (hc : w.cmds = some cs) : goodCmds S cs := by
  have hcs : (instVal w).cmds = cs := by simp [instVal, hc]
  rcases hS.2.stRange i hi x w hw with h | h | h | h
  · exact absurd h hst
  · have hv := hS.2.recVote i hi x w hw (Or.inl h)
    obtain ⟨ℓ, v0, hph, heq⟩ := (lk_votes hS).1 i x _ _ _ hv h
    rw [← hcs, heq]; exact valOk_good hS (Or.inl hph)
  · have hv := hS.2.recVote i hi x w hw (Or.inr h)
    rw [h] at hv
    obtain ⟨ℓ, hacc⟩ := (lk_votes hS).2 i x _ _ hv
    rw [← hcs]; exact valOk_good hS (Or.inr hacc)
  · obtain ⟨-, hcv⟩ := (lk_agreement hS).2 i hi x w hw h
    rw [← hcs]; exact committed_good hS hcv

theorem getOrDefault_cases (τ : RState) (x : InstId) :
    (getOrDefault τ x).2 = newInstanceDefault x ∨ τ.inst x = some (getOrDefault τ x).2 := by
  unfold getOrDefault; split
  · right; assumption
  · left; rfl

/-- `handlePrepare`'s reply (the record's commands and deps; empty for NONE, `NR`). -/
theorem prepare_outsWf [GooseExts] [GoGlobalContext] {S : Sys} (hS : Inv S) (hX : InvX S) (hops : opsPre S)
    {i : Nat} (hi : i < nR) (m : Prepare) : OutsWf (hPrepare (S.rep i) m).2 := by
  have key : ∀ w0 : InstRec, (w0 = newInstanceDefault ⟨toN m.replica, toN m.inst⟩ ∨
      (S.rep i).inst ⟨toN m.replica, toN m.inst⟩ = some w0) →
      cmdsWf (w0.cmds.getD []) ∧ depsWf w0.deps := by
    intro w0 hw0
    rcases hw0 with rfl | hw
    · simp [newInstanceDefault, cmdsWf, depsWf]
    · by_cases hst : w0.status = stNONE
      · obtain ⟨h1, h2⟩ := hX.1 i _ w0 hw hst
        rw [h1, h2]; simp [cmdsWf, depsWf]
      · refine ⟨?_, depsWf_of_ok ((hS.1.1.2.1 i hi _ w0 hw).2.2.2.1 hst)⟩
        cases hc : w0.cmds with
        | none => simp [cmdsWf]
        | some cs => exact cmdsWf_of_good hS hX hops (rec_good hS hi hw hst hc)
  intro o ho
  unfold hPrepare at ho
  dsimp only at ho
  simp only [List.mem_singleton] at ho
  subst ho
  have hc := getOrDefault_cases (bumpRecvBallot (S.rep i) m.ballot) ⟨toN m.replica, toN m.inst⟩
  simp only [bumpRecvBallot_inst'] at hc
  show cmdsWf _ ∧ depsWf _
  split
  · exact key (getOrDefault (bumpRecvBallot (S.rep i) m.ballot) ⟨toN m.replica, toN m.inst⟩).2 hc
  · exact key _ hc

/-- Outputs that are events, re-proposals and AcceptReplies are encodable. -/
def Quiet (o : Out) : Prop :=
  (∃ e, o = .ev e) ∨ (∃ p, o = .repropose p) ∨ ∃ t r, o = .send t (.acceptReply r)

theorem outsWf_quiet {outs : List Out} (h : ∀ o ∈ outs, Quiet o) : OutsWf outs := by
  intro o ho
  rcases h o ho with ⟨e, rfl⟩ | ⟨p, rfl⟩ | ⟨t, r, rfl⟩ <;> trivial

theorem hAccept_quiet (σ : RState) (m : Accept) : ∀ o ∈ (hAccept σ m).2, Quiet o := by
  intro o ho
  unfold hAccept at ho
  dsimp only at ho
  repeat' split at ho
  all_goals first
    | (simp at ho; done)
    | (simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil,
        or_false] at ho
       rcases ho with rfl | rfl
       · exact Or.inl ⟨_, rfl⟩
       · exact Or.inr (Or.inr ⟨_, _, rfl⟩))
    | (simp only [List.mem_append, List.mem_singleton, List.nil_append] at ho
       subst ho; exact Or.inr (Or.inr ⟨_, _, rfl⟩))

theorem hCommit_quiet (σ : RState) (m : Commit) : ∀ o ∈ (hCommit σ m).2, Quiet o := by
  intro o ho
  unfold hCommit at ho
  dsimp only at ho
  repeat' split at ho
  all_goals first
    | (simp at ho; done)
    | (rcases List.mem_append.mp ho with ho | ho
       · first
           | (simp at ho; done)
           | (obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho; exact Or.inr (Or.inl ⟨_, rfl⟩))
       · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
         rcases ho with rfl | rfl <;> exact Or.inl ⟨_, rfl⟩)

theorem hPreAccept_nob (σ : RState) (m : PreAccept) : ∀ b, Out.bcast b ∉ (hPreAccept σ m).2 := by
  intro b h
  unfold hPreAccept at h
  dsimp only at h
  repeat' split at h
  all_goals simp at h

theorem lk_pendingKind {S : Sys} (h : Inv S) : Inv.pendingKind S := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h.1; exact h

/-- **Every message a delivery's step sends or broadcasts is encodable.** -/
theorem deliver_outsWf_of [GooseExts] [GoGlobalContext] {fr i n : Nat} {m : Msg} {σ : RState}
    (h : deliverPre fr i n m σ) (hpo : σ.peerOrder ≠ []) : OutsWf (hMsg σ m).2 := by
  obtain ⟨S, hS, hi, hfr, hidle, hσ, hm, hnd, hX, hops⟩ := h
  subst hσ
  have hS' := inv_step_deliver S fr i n m hS hi hfr hidle hm hnd
  have hstep := Step.deliver S fr i n m hi hfr hidle hm hnd
  have hX' : InvX (S.deliver fr i n m) := ⟨NR_step hstep hX.1, fun y ps hy => hX.2 y ps (by
    unfold Sys.deliver at hy; rwa [applyStep_owner'] at hy)⟩
  have hops' : opsPre (S.deliver fr i n m) := by
    intro o ho; apply hops
    unfold Sys.deliver Sys.applyStep at ho; rw [Sys.foldl_emit_ops] at ho; exact ho
  have hpm := applyStep_outs_msgs { S with delivered := S.delivered ++ [(fr, i, n)] } i
    (hMsg (S.rep i) m) hidle.1
  have gen : GoodO (hMsg (S.rep i) m).2 → OutsWf (hMsg (S.rep i) m).2 := by
    intro hg o ho
    cases o with
    | send t m' =>
      exact msg_wf hS' hX' hops' (hpm.1 t m' ho) (hg.1 t m' ho).1 (hg.1 t m' ho).2
    | bcast b =>
      obtain ⟨hl, hs, hp⟩ := hg.2 b ho
      obtain ⟨hpend, p, hb⟩ := hpm.2 b ho hl hs hp
      have hk := lk_pendingKind hS' i b hpend
      refine msg_wf hS' hX' hops' hb (fun q e => ?_) (fun q e => ?_) <;>
        rw [e] at hk <;> simp [Msg.isBcast] at hk
    | _ => trivial
  cases m with
  | prepare p => exact prepare_outsWf hS hX hops hi p
  | prepareReply p => exact gen (hPrepareReply_good hpo p)
  | preAcceptReply p => exact gen (hPreAcceptReply_good hpo p)
  | acceptReply p => exact gen (hAcceptReply_good hpo p)
  | accept p => exact outsWf_quiet (hAccept_quiet _ p)
  | commit p => exact outsWf_quiet (hCommit_quiet _ p)
  | preAccept p =>
    intro o ho
    cases o with
    | send t m' =>
      obtain ⟨r, rfl, hcd⟩ := hPreAccept_sends _ p t _ ho
      have hmm := hpm.1 t _ ho
      exact ⟨depsWf_of_ok ((hS'.1.2.1 i t _ hmm).2 _ (by simp [Msg.depsFields])),
        by unfold depsWf; rw [hcd]; unfold nR; decide⟩
    | bcast b => exact absurd ho (hPreAccept_nob _ p b)
    | _ => trivial
  | tryPreAccept p => intro o ho; simp [hMsg, hTryPreAccept] at ho
  | tryPreAcceptReply p => intro o ho; simp [hMsg, hTryPreAcceptReply] at ho
  | beacon _ => intro o ho; simp [hMsg] at ho
  | beaconReply _ => intro o ho; simp [hMsg] at ho

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
