/-
`handlePrepareReply`'s decision (the recovery's `(N+1)/2`-th distinct reply at its ballot): the
handler's result (`dec_eq`, `dOut`), the decision's report list (`dec_reports`: a
`DecideProof.Reports`), and sub-case 1 (`inv_deliver_dec1`: commit of the reported committed
value, `RecCommitProof.inv_commit_known`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.RecPhase1
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPrepReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HCommit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Decide
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.CmdDecide

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace DecideStepProof

open HStepProof HLocal SafeProof AuxProof PrepReplyProof RecCommitProof

/-! ## The decision's result -/

/-- The replies the decision reads. -/
def dReps (lb : LbRec) (p : PrepareReply) : List PReply := lb.prepareReplies ++ [⟨p, false⟩]

/-- `lb.leaderResponded` after the loop. -/
def dLr (lb : LbRec) (p : PrepareReply) : Bool :=
  Bool.or lb.leaderResponded <| (dReps lb p).any (fun e => e.m.acceptorId == e.m.replica)

/-- `maxVbal`. -/
def dMx (lb : LbRec) (p : PrepareReply) : w32 :=
  (dReps lb p).foldl (fun mx e => if mx.slt e.m.vballot then e.m.vballot else mx) (W32 (-1))

/-- The sub-case and the chosen reply. -/
def dD (lb : LbRec) (p : PrepareReply) : Nat × Option PReply :=
  prepDecide (dReps lb p) (dMx lb p) (dLr lb p) p.replica

/-- The bookkeeping after the decision (before the sub-case's status). -/
def dLb (lb : LbRec) (p : PrepareReply) : LbRec :=
  match (dD lb p).2 with
  | some e => { lb with prepareReplies := dReps lb p, preparing := false,
                        leaderResponded := dLr lb p, ballot := dMx lb p,
                        cmds := if e.cmdsNil then none else some e.m.command,
                        seq := e.m.seq, deps := e.m.deps, status := e.m.status }
  | none => { lb with prepareReplies := dReps lb p, preparing := false,
                      leaderResponded := dLr lb p, ballot := dMx lb p,
                      cmds := some noop, status := stNONE }

/-- The record after the decision (before the sub-case's status). -/
def dInst (w : InstRec) (lb : LbRec) (p : PrepareReply) : InstRec :=
  { w with cmds := (dLb lb p).cmds, bal := (dLb lb p).lastTriedBallot,
           vbal := (dLb lb p).lastTriedBallot,
           seq := (dLb lb p).seq, deps := (dLb lb p).deps, status := (dLb lb p).status }

/-- The handler's result when it decides. -/
def dOut (σ : RState) (p : PrepareReply) (w : InstRec) (lb : LbRec) : RState × List Out :=
  let x : InstId := ⟨toN p.replica, toN p.inst⟩
  let σb := bumpRecvBallot σ p.ballot
  if (dD lb p).1 = 1 then
    let inst := { dInst w lb p with status := stCOMMITTED,
                                     lb := some { dLb lb p with status := stCOMMITTED } }
    (updateCommitted (σb.setInst x inst) x.q,
      [Out.ev (.commit x inst.bal (⟨inst.cmds.getD [], inst.seq, inst.deps⟩ : Val))])
  else if (dD lb p).1 = 2 ∨ (dD lb p).1 = 3 then
    let lb' := { dLb lb p with status := stACCEPTED }
    let inst := { dInst w lb p with status := stACCEPTED, lb := some lb' }
    (σb.setInst x inst, [Out.ev (.vote x lb'.lastTriedBallot stACCEPTED (lbVal lb')),
      Out.ev (.accept x lb'.lastTriedBallot (lbVal lb')),
      Out.bcast (bcastAcceptOf (σb.setInst x inst) x (acceptOf (σb.setInst x inst) p.replica p.inst lb'))])
  else
    startPhase1 (σb.setInst x { dInst w lb p with lb := some (dLb lb p) }) ((dLb lb p).cmds.getD [])
      x p.replica p.inst (dLb lb p).lastTriedBallot (dLb lb p).clientProposals

theorem dec_eq (σ : RState) (p : PrepareReply) (w : InstRec) (lb : LbRec)
    (hw : σ.inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
    (hp : lb.preparing = true) (h2 : stGe w.status stCOMMITTED = false)
    (h3 : lb.lastTriedBallot.slt w.bal = false) (h4 : p.ballot = lb.lastTriedBallot)
    (h5 : lb.prepareReplies.any (fun e => e.m.acceptorId == p.acceptorId) = false)
    (h6 : ¬ (lb.prepareReplies ++ [(⟨p, false⟩ : PReply)]).length < (nR + 1) / 2) :
    hPrepareReply σ p = dOut σ p w lb := by
  unfold hPrepareReply
  simp only [hw, hlb]
  rw [if_neg (by simp [hp]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg h6]
  rfl

theorem dLb_fields (lb : LbRec) (p : PrepareReply) :
    (dLb lb p).lastTriedBallot = lb.lastTriedBallot ∧ (dLb lb p).clientProposals = lb.clientProposals ∧
    (dLb lb p).preparing = false ∧ (dLb lb p).ballot = dMx lb p ∧
    (dLb lb p).tryingToPreAccept = lb.tryingToPreAccept ∧
    (dLb lb p).preAcceptOKs = lb.preAcceptOKs ∧ (dLb lb p).acceptOKs = lb.acceptOKs ∧
    (dLb lb p).prepareReplies = dReps lb p ∧ (dLb lb p).leaderResponded = dLr lb p ∧
    (dLb lb p).allEqual = lb.allEqual ∧ (dLb lb p).preAcceptsSent = lb.preAcceptsSent := by
  unfold dLb; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dLb_some (lb : LbRec) (p : PrepareReply) (e : PReply) (h : (dD lb p).2 = some e) :
    (dLb lb p).cmds = (if e.cmdsNil then none else some e.m.command) ∧ (dLb lb p).seq = e.m.seq ∧
    (dLb lb p).deps = e.m.deps ∧ (dLb lb p).status = e.m.status := by
  unfold dLb; rw [h]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem prepDecide_mem (reps : List PReply) (mx : w32) (lr : Bool) (rep : w32) (e : PReply)
    (h : (prepDecide reps mx lr rep).2 = some e) : e ∈ reps := by
  unfold prepDecide at h
  split at h
  · rename_i e' he; cases h; exact List.mem_of_find?_eq_some he
  split at h
  · rename_i e' he; cases h; exact List.mem_of_find?_eq_some he
  split at h
  · rename_i e' he; cases h
    split at he
    · exact List.mem_of_find?_eq_some he
    · cases he
  split at h
  · rename_i e' he; cases h; exact List.mem_of_find?_eq_some he
  · cases h

theorem prepDecide_one (reps : List PReply) (mx : w32) (lr : Bool) (rep : w32)
    (h : (prepDecide reps mx lr rep).1 = 1) :
    ∃ e, (prepDecide reps mx lr rep).2 = some e ∧ stGe e.m.status stCOMMITTED = true := by
  cases hf : reps.find? (fun e => stGe e.m.status stCOMMITTED) with
  | some e => exact ⟨e, by simp [prepDecide, hf], by simpa using List.find?_some hf⟩
  | none =>
    exfalso
    simp only [prepDecide, hf] at h
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    · simp at h

theorem stGe_com {s : w8} (hs : s = stNONE ∨ isPA s ∨ s = stACCEPTED ∨ isCommitted s)
    (h : stGe s stCOMMITTED = true) : isCommitted s := by
  rcases hs with rfl | (rfl | rfl) | rfl | hc
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact hc

theorem inv_reports {S : Sys} (hS : Inv S) : Inv.reports S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hS.1; h

theorem inv_rr {S : Sys} (hS : Inv S) : Inv.repliesReportVotes S :=
  let ⟨_, _, _, _, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_lb {S : Sys} (hS : Inv S) : Inv.lbInv S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_own {S : Sys} (hS : Inv S) : Inv.ballotOwner S :=
  let ⟨_, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_wf {S : Sys} (hS : Inv S) : Inv.wf S := hS.1.1

theorem inv_vf {S : Sys} (hS : Inv S) : Inv.votesFollowProposals S :=
  let ⟨_, _, _, _, _, _, _, h, _⟩ := hS.1; h

theorem raw_of (q : w32) (h0 : 0 ≤ zz q) (h1 : zz q < nR) : q = W32 (toN q) :=
  eq_W32_of_zz q _ (by omega) (by simp only [nR] at h1; have := toN_of_zz q h0; omega)
    (toN_of_zz q h0).symm

/-! ## The replies the decision reads -/

section
variable (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
  (p : PrepareReply) (hm : (S.sent fr i)[n]? = some (.prepareReply p))
  (w : InstRec) (lb : LbRec)
  (hw : (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
  (hp : lb.preparing = true) (h4 : p.ballot = lb.lastTriedBallot)
include hS hi hfr hm hw hlb hp h4

/-- Every reply the decision reads is a report at the recovery's ballot about `x`, of a replica,
with `nil` commands only if NONE, and followable deps and commands if not NONE. -/
theorem entry_report : ∀ e ∈ dReps lb p,
    (∃ E, S.prepReport (toN e.m.acceptorId) e.m E) ∧ toN e.m.acceptorId < nR ∧
    e.m.ballot = lb.lastTriedBallot ∧
    (⟨toN e.m.replica, toN e.m.inst⟩ : InstId) = ⟨toN p.replica, toN p.inst⟩ ∧
    (e.cmdsNil = true → e.m.status = stNONE) ∧
    (e.m.status ≠ stNONE → depsOk e.m.deps ∧ e.m.command ≠ []) ∧
    e.m.replica = W32 (toN e.m.replica) := by
  have hpm := mem_msgs_of_sent S hm
  have hA := hS.2
  have fromMsg : ∀ a (m : PrepareReply), m ∈ [] ∨ Msg.prepareReply m ∈ S.msgs a i →
      (∃ E, S.prepReport a m E) ∧ a < nR ∧
      (m.status ≠ stNONE → depsOk m.deps ∧ m.command ≠ []) ∧ m.replica = W32 (toN m.replica) := by
    rintro a m (h | h)
    · cases h
    have hs := hA.prSent a i m h
    obtain ⟨r1, r2, -, -⟩ := (hS.1.2.1 a i _ h).1 m.replica m.inst rfl
    refine ⟨⟨_, hs, Or.inl ⟨i, h, rfl⟩⟩, (hS.1.1.2.2.2.2.2.1 a i (List.ne_nil_of_mem h)).1,
      fun hn => ⟨(hS.1.2.1 a i _ h).2 m.deps (by simp [Msg.depsFields, hn]),
        hA.cmdsNe.2.2.2.1 a i m h hn⟩, raw_of _ r1 r2⟩
  intro e he
  simp only [dReps, List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · obtain ⟨-, -, -, -, -, -, -, -, a9⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.1 i hi _ w lb hw hlb
    obtain ⟨-, a9⟩ := a9 hp
    obtain ⟨d1, d2, d3⟩ := a9 e he
    have hnil := (hA.prepNoProp i hi _ w lb hw hlb hp).2.2.2.1 e he
    simp only [Msg.instOf, Option.some.injEq] at d2
    rcases d3 with ⟨-, k, hk1, -⟩ | ⟨e1, e2⟩
    · obtain ⟨c1, c2, c3, c4⟩ := fromMsg _ e.m (Or.inr (mem_msgs_of_sent S hk1))
      exact ⟨c1, c2, d1, d2, hnil, c3, c4⟩
    · refine ⟨⟨_, by rw [e1]; exact e2, Or.inr rfl⟩, by rw [e1]; exact hi, d1, d2, hnil,
        fun hn => ⟨hA.selfOk i e.m e2 hn, hA.cmdsNe.2.2.2.2.1 i e.m e2 hn⟩, hA.selfRaw i e.m e2⟩
  · have hrep : S.prepReport fr p (.sent i (.prepareReply p)) :=
      ⟨hA.prSent fr i p hpm, Or.inl ⟨i, hpm, rfl⟩⟩
    have hacc := (hS.1.2.2.2.2.2.2.2.2.1.1 fr p _ hrep).1
    obtain ⟨-, -, c3, c4⟩ := fromMsg fr p (Or.inr hpm)
    refine ⟨⟨_, by rw [hacc, toN_W32 fr hfr]; exact hrep⟩, by rw [hacc, toN_W32 fr hfr]; exact hfr,
      h4, rfl, fun h => (by cases h), c3, c4⟩

/-- `maxVbal` is at most the recovery's ballot. -/
theorem dMx_le (hlt : (nR : Int) ≤ zz lb.lastTriedBallot) :
    zz (dMx lb p) ≤ zz lb.lastTriedBallot := by
  have hf := DecideProof.foldl_max (dReps lb p) (W32 (-1))
  have heq : dMx lb p = (dReps lb p).foldl DecideProof.maxStep (W32 (-1)) := rfl
  rw [heq]
  rcases hf.2.2 with h | ⟨e, he, h⟩
  · rw [h]; have : zz (W32 (-1)) = -1 := by decide
    rw [this]; omega
  · rw [← h]
    obtain ⟨⟨E, hE⟩, -, hb, -⟩ := entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e he
    have := (inv_reports hS).2.2.2.2.2.2.2.2 _ e.m E hE
    rw [← hb]; exact this

end

/-! ## Sub-case 1 -/

/-- **Sub-case 1**: a reply reports the instance committed; the replica commits its value. -/
theorem inv_deliver_dec1 (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (p : PrepareReply) (hm : (S.sent fr i)[n]? = some (.prepareReply p))
    (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
    (hp : lb.preparing = true) (h2 : stGe w.status stCOMMITTED = false)
    (h3 : lb.lastTriedBallot.slt w.bal = false) (h4 : p.ballot = lb.lastTriedBallot)
    (h5 : lb.prepareReplies.any (fun e => e.m.acceptorId == p.acceptorId) = false)
    (h6 : ¬ (lb.prepareReplies ++ [(⟨p, false⟩ : PReply)]).length < (nR + 1) / 2)
    (h1 : (dD lb p).1 = 1) : Inv (S.deliver fr i n (.prepareReply p)) := by
  generalize hx : (⟨toN p.replica, toN p.inst⟩ : InstId) = x at hw
  obtain ⟨e, he, hst⟩ := prepDecide_one _ _ _ _ h1
  have heR : e ∈ dReps lb p := prepDecide_mem _ _ _ _ e he
  have hw0 := hw; rw [← hx] at hw0
  obtain ⟨⟨E, hE⟩, -, -, hex, hnil, hok, -⟩ :=
    entry_report S fr i n hS hi hfr p hm w lb hw0 hlb hp h4 e heR
  have hpN := hS.2.prepNoProp i hi x w lb hw hlb hp
  have hcom : isCommitted e.m.status :=
    stGe_com ((inv_reports hS).1 _ e.m E hE) hst
  have hnn : e.m.status ≠ stNONE := by intro h; rw [h] at hcom; rcases hcom with h | h <;> cases h
  obtain ⟨hdeps, hcne⟩ := hok hnn
  have hcf : e.cmdsNil = false := by
    cases h : e.cmdsNil
    · rfl
    · exact absurd (hnil h) hnn
  have hcv : S.committedVal x ⟨e.m.command, e.m.seq, e.m.deps⟩ := by
    have := ((inv_rr hS).1 _ e.m E hE).2.2.1 hcom
    rw [hex, hx] at this; exact this
  obtain ⟨l1, l2, l3, l4⟩ := dLb_some lb p e he
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -⟩ := dLb_fields lb p
  rw [hcf] at l1; simp only [Bool.false_eq_true, if_false] at l1
  have hlbI := inv_lb hS i hi x w lb hw hlb
  -- the step
  have hH := hs_deliver S fr i n (.prepareReply p) hidle hm
  have hout : hMsg (S.rep i) (.prepareReply p) =
      (updateCommitted ((bumpRecvBallot (S.rep i) p.ballot).setInst x
          (comKnown w { dLb lb p with status := stCOMMITTED } lb.lastTriedBallot
            ⟨e.m.command, e.m.seq, e.m.deps⟩)) x.q,
        [Out.ev (.commit x lb.lastTriedBallot ⟨e.m.command, e.m.seq, e.m.deps⟩)]) := by
    simp only [hMsg]
    rw [dec_eq (S.rep i) p w lb (by rw [hx]; exact hw) hlb hp h2 h3 h4 h5 h6]
    unfold dOut
    rw [if_pos h1]
    subst hx
    simp only [dInst, comKnown]
    generalize dLb lb p = L at l1 l2 l3 f1 ⊢
    cases L; simp only at l1 l2 l3 f1; subst l1 l2 l3 f1; rfl
  rw [hout] at hH
  have hH' : HS S (S.deliver fr i n (.prepareReply p)) i
      (updateCommitted ((bumpRecvBallot (S.rep i) p.ballot).setInst x
          (comKnown w { dLb lb p with status := stCOMMITTED } lb.lastTriedBallot
            ⟨e.m.command, e.m.seq, e.m.deps⟩)) x.q)
      [.commit x lb.lastTriedBallot ⟨e.m.command, e.m.seq, e.m.deps⟩] (fun _ => []) none := by
    have hev : evsOf [Out.ev (.commit x lb.lastTriedBallot ⟨e.m.command, e.m.seq, e.m.deps⟩)] =
        [.commit x lb.lastTriedBallot ⟨e.m.command, e.m.seq, e.m.deps⟩] := rfl
    have hsd : sendsOf [Out.ev (.commit x lb.lastTriedBallot ⟨e.m.command, e.m.seq, e.m.deps⟩)] =
        fun _ => [] := by funext to; rfl
    have hpd : pendFold [Out.ev (.commit x lb.lastTriedBallot ⟨e.m.command, e.m.seq, e.m.deps⟩)]
        none = none := rfl
    rw [hev, hsd, hpd] at hH; exact hH
  refine inv_commit_known S _ i _ x w lb { dLb lb p with status := stCOMMITTED } lb.lastTriedBallot _ hS hi hidle hH'
    (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h))
    (by simp [RState.setInst]) (by simp [RState.setInst, updateCommitted])
    (AuxProof.bumpRB_cls _ _) hw hlb
    (DecideProof.notCommitted_of_stGe h2) ((slt_false _ _).mp h3) (Int.le_refl _)
    (by have := hpN.1; omega) hcv hdeps hcne ?_ (by
      have hxq : x.q < nR := ((inv_wf hS).2.1 i hi x w hw).2.1
      have := hpN.1; rw [zz_initBal x hxq]; simp only [nR] at hxq this ⊢; omega)
  refine ⟨by simp [f1], ?_, rfl, by simp [f3], by simp [f5]; exact hlbI.2.2.1, by simp [f2],
    by simp [f6], by simp [f7], by simp [l3]; exact hdeps, by simp [l1]⟩
  simp only [f4]
  exact dMx_le S fr i n hS hi hfr p hm w lb (by rw [hx]; exact hw) hlb hp h4 hpN.1

/-! ## The decision's preconditions (`DecideProof.decide_safe`) -/


section
variable (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
  (p : PrepareReply) (hm : (S.sent fr i)[n]? = some (.prepareReply p))
  (w : InstRec) (lb : LbRec)
  (hw : (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
  (hp : lb.preparing = true) (h4 : p.ballot = lb.lastTriedBallot)
include hS hi hfr hm hw hlb hp h4

/-- The decision's replies are reports at the recovery's ballot (`DecideProof.Reports`). -/
theorem dec_reports
    (h5 : lb.prepareReplies.any (fun e => e.m.acceptorId == p.acceptorId) = false)
    (h6 : ¬ (lb.prepareReplies ++ [(⟨p, false⟩ : PReply)]).length < (nR + 1) / 2) :
    DecideProof.Reports S ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot (dReps lb p) := by
  refine ⟨?_, by simp only [dReps]; omega, fun e he => ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, -, a9⟩ := inv_lb hS i hi _ w lb hw hlb
    obtain ⟨d1, -⟩ := a9 hp
    simp only [dReps, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨d1, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro a ha b hb' hab
    simp only [List.mem_singleton] at hb'
    obtain ⟨e, he, hea⟩ := List.mem_map.mp ha
    have := List.any_eq_false.mp h5 e he
    rw [hea, hab, hb'] at this; simp at this
  · obtain ⟨⟨E, hE⟩, hacc, hb, hx, -, -, hraw⟩ :=
      entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e he
    simp only [InstId.mk.injEq] at hx
    refine ⟨hacc, hb, by rw [hraw, hx.1], by simp only [Aux.repX, hx.1, hx.2], E, hE⟩

/-- No vote at the recovery's ballot yet. -/
theorem dec_nov : ∀ r st u, isPA st → ¬ S.ev r (.vote ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot st u) := by
  intro r st u hst hv
  have hown := (inv_own hS)
  have hxq : (toN p.replica) < nR := (inv_wf hS).2.1 i hi _ w hw |>.2.1
  have hmk := (inv_lb hS i hi _ w lb hw hlb).1
  obtain ⟨ℓ, v0, hph, -⟩ := (inv_vf hS).1 r _ _ st u hv hst
  obtain ⟨p1, p2, -, hp1, -⟩ := hown.2.1 ℓ _ _ v0 hph
  have := maker_eq S hown hxq (List.mem_of_getElem? hp1) hmk
  subst this
  exact (hS.2.prepNoProp _ hi _ w lb hw hlb hp).2.1 v0 hph

/-- No Phase 1 and no Accept at the recovery's ballot yet (by anyone: only its maker proposes
there). -/
theorem dec_noprop : (∀ r u, ¬ S.ev r (.phase1 ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot u)) ∧
    (∀ r u, ¬ S.ev r (.accept ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot u)) := by
  have hown := (inv_own hS)
  have hxq : (toN p.replica) < nR := (inv_wf hS).2.1 i hi _ w hw |>.2.1
  have hmk := (inv_lb hS i hi _ w lb hw hlb).1
  have hpn := hS.2.prepNoProp _ hi _ w lb hw hlb hp
  refine ⟨fun r u hph => ?_, fun r u hac => ?_⟩
  · obtain ⟨p1, p2, -, hp1, -⟩ := hown.2.1 r _ _ u hph
    have := maker_eq S hown hxq (List.mem_of_getElem? hp1) hmk
    subst this; exact hpn.2.1 u hph
  · have := maker_eq S hown hxq (hown.2.2.1 r _ _ u hac) hmk
    subst this; exact hpn.2.2.1 u hac

end

theorem prepDecide_23 (reps : List PReply) (mx : w32) (lr : Bool) (rep : w32)
    (h : (prepDecide reps mx lr rep).1 = 2 ∨ (prepDecide reps mx lr rep).1 = 3) :
    ∃ e, (prepDecide reps mx lr rep).2 = some e ∧ (e.m.status = stACCEPTED ∨ isPA e.m.status) := by
  rcases DecideProof.prepDecide_cases reps mx lr rep with h1 | ⟨-, ⟨-, e, hde, -, -, hes⟩ |
    ⟨-, ⟨-, -, -, e, hde, -, hok⟩ | ⟨-, n2, n3, -⟩⟩⟩
  · omega
  · exact ⟨e, hde, Or.inl hes⟩
  · refine ⟨e, hde, Or.inr ?_⟩
    simp only [subCase3Ok, isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    exact hok.1.1.2
  · omega

/-! ## Sub-cases 2 and 3 -/

/-- The chosen reply of sub-case 2 (ACCEPTED at `maxVbal`) or 3 (`subCase3Ok` at the initial
ballot). -/
theorem prepDecide_23e (reps : List PReply) (mx : w32) (lr : Bool) (rep : w32) (e : PReply)
    (he : (prepDecide reps mx lr rep).2 = some e)
    (h : (prepDecide reps mx lr rep).1 = 2 ∨ (prepDecide reps mx lr rep).1 = 3) :
    (e.m.vballot = mx ∧ e.m.status = stACCEPTED) ∨
    (isInitialBallot mx rep = true ∧ subCase3Ok reps mx e = true) := by
  rcases DecideProof.prepDecide_cases reps mx lr rep with h1 | ⟨-, ⟨-, e', hde, -, hev, hes⟩ |
    ⟨-, ⟨-, hib, -, e', hde, -, hok⟩ | ⟨-, n2, n3, -⟩⟩⟩
  · omega
  · rw [hde] at he; cases he; exact Or.inl ⟨hev, hes⟩
  · rw [hde] at he; cases he; exact Or.inr ⟨hib, hok⟩
  · omega

theorem sub3_e {reps : List PReply} {mx : w32} {e : PReply} (hok : subCase3Ok reps mx e = true) :
    e.m.vballot = mx ∧ isPA e.m.status := by
  simp only [subCase3Ok, isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
  exact ⟨hok.1.1.1, hok.1.1.2⟩

/-- The accepted value's commands were proposed at `maxVbal` (the chosen reply's vote). -/
theorem dec23_prop (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (p : PrepareReply) (hm : (S.sent fr i)[n]? = some (.prepareReply p))
    (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
    (hp : lb.preparing = true) (h4 : p.ballot = lb.lastTriedBallot) (e : PReply)
    (he : (dD lb p).2 = some e) (heR : e ∈ dReps lb p) (h23 : (dD lb p).1 = 2 ∨ (dD lb p).1 = 3)
    (hst : e.m.status = stACCEPTED ∨ isPA e.m.status)
    (f4 : (dLb lb p).ballot = dMx lb p) :
    S.propAt ⟨toN p.replica, toN p.inst⟩ ({ dLb lb p with status := stACCEPTED } : LbRec).ballot
      e.m.command := by
  obtain ⟨⟨E, hE⟩, -, -, hex, -, -, -⟩ :=
    entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e heR
  have hvb : e.m.vballot = dMx lb p ∧ (isPA e.m.status ∨ e.m.status = stACCEPTED) := by
    rcases prepDecide_23e (dReps lb p) (dMx lb p) (dLr lb p) p.replica e he h23 with
      ⟨h1, h2⟩ | ⟨-, hok⟩
    · exact ⟨h1, Or.inr h2⟩
    · obtain ⟨a, b⟩ := sub3_e hok; exact ⟨a, Or.inl b⟩
  have hv := DecideProof.rep_reported (inv_rr hS) hex hE hvb.2
  show S.propAt _ (dLb lb p).ballot _
  rw [f4, ← hvb.1]
  exact Or.inl ⟨_, _, _, hvb.2, hv, rfl⟩

/-- The accepted value is witnessed (sub-case 2: the reported Accept's value, `accWit`;
sub-case 3: the two identical pre-accept reports' voters and the leader's Phase 1), or the
instance is decided. -/
theorem dec23_wit (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (p : PrepareReply) (hm : (S.sent fr i)[n]? = some (.prepareReply p))
    (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
    (hp : lb.preparing = true) (h2 : stGe w.status stCOMMITTED = false)
    (h3 : lb.lastTriedBallot.slt w.bal = false) (h4 : p.ballot = lb.lastTriedBallot)
    (h5 : lb.prepareReplies.any (fun e => e.m.acceptorId == p.acceptorId) = false)
    (h6 : ¬ (lb.prepareReplies ++ [(⟨p, false⟩ : PReply)]).length < (nR + 1) / 2)
    (h1 : ¬ (dD lb p).1 = 1) (h23 : (dD lb p).1 = 2 ∨ (dD lb p).1 = 3) :
    ∀ e, (dD lb p).2 = some e → e.m.command ≠ noop →
      S.witnessed ⟨toN p.replica, toN p.inst⟩ ⟨e.m.command, e.m.seq, e.m.deps⟩ ∨
      ∃ u, S.committedVal ⟨toN p.replica, toN p.inst⟩ u := by
  intro e he hnoop
  have hrr := inv_rr hS
  have hvf := inv_vf hS
  have hown := inv_own hS
  obtain ⟨-, -, -, -, -, -, hop, -⟩ := hS.1
  have hxq : toN p.replica < nR := (inv_wf hS).2.1 i hi _ w hw |>.2.1
  have hpm := mem_msgs_of_sent S hm
  obtain ⟨r1, r2, -, -⟩ := (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
  have hpraw : p.replica = W32 (toN p.replica) := raw_of _ r1 r2
  have heR : e ∈ dReps lb p := prepDecide_mem _ _ _ _ e he
  obtain ⟨⟨E, hE⟩, -, -, hex, -, hoke, -⟩ :=
    entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e heR
  rcases prepDecide_23e (dReps lb p) (dMx lb p) (dLr lb p) p.replica e he h23 with
    ⟨-, hst⟩ | ⟨hib, hok⟩
  · -- sub-case 2: the reported Accept's value
    have hv := DecideProof.rep_reported hrr hex hE (Or.inr hst)
    rw [hst] at hv
    obtain ⟨ℓ, hl⟩ := hvf.2 _ _ _ _ hv
    exact hS.2.pm.accWit ℓ _ _ _ hl hnoop
  · -- sub-case 3: two identical non-leader pre-accept votes and the leader's Phase 1
    left
    have hmx : dMx lb p = initBal ⟨toN p.replica, toN p.inst⟩ := by
      simp only [isInitialBallot, beq_iff_eq] at hib; rw [hib]; exact hpraw
    rw [hmx] at hok
    obtain ⟨hvbe, hpaE⟩ := sub3_e hok
    have hnne : e.m.status ≠ stNONE := fun h => by rw [h] at hpaE; revert hpaE; unfold isPA; decide
    have hdl : e.m.deps.length = nR := (hoke hnne).1.1
    have hve := DecideProof.rep_reported hrr hex hE (Or.inl hpaE)
    rw [hvbe] at hve
    obtain ⟨ℓe, v0e, hphe, hce⟩ := hvf.1 _ _ _ _ _ hve hpaE
    simp only at hce
    have hℓe : ℓe = toN p.replica := by
      obtain ⟨p1, p2, -, hp1, -⟩ := hown.2.1 _ _ _ _ hphe
      rcases (hown.1 _ _ _ (List.mem_of_getElem? hp1)).1 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [zz_initBal _ hxq] at h; simp [nR] at h hxq; omega
    have hlead := hS.2.pm.phAttrs _ _ _ _ hphe
    have hge := hS.2.pm.paGe _ _ _ _ _ _ _ hpaE hve hphe
    rw [hℓe] at hlead
    have hR := dec_reports S fr i n hS hi hfr p hm w lb hw hlb hp h4 h5 h6
    simp only [subCase3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨-, hlen⟩ := hok
    obtain ⟨R, hRdef⟩ : ∃ R, R = (dReps lb p).filter (fun o =>
        isPreAcceptedAt (initBal ⟨toN p.replica, toN p.inst⟩) o &&
        o.m.acceptorId != o.m.replica && o.m.seq == e.m.seq && depsEqual o.m.deps e.m.deps) :=
      ⟨_, rfl⟩
    rw [← hRdef] at hlen
    have hent : ∀ o ∈ R, toN o.m.acceptorId < nR ∧ toN o.m.acceptorId ≠ toN p.replica ∧
        S.ev (toN o.m.acceptorId) (.attrsRec ⟨toN p.replica, toN p.inst⟩ e.m.command e.m.deps) := by
      intro o ho
      rw [hRdef, List.mem_filter] at ho
      obtain ⟨hor, hpo⟩ := ho
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hpo
      obtain ⟨⟨⟨hpo, hneq⟩, -⟩, hdeq⟩ := hpo
      have hpaO : isPA o.m.status := by
        simp only [isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpo
        exact hpo.2
      have hvbo : o.m.vballot = initBal ⟨toN p.replica, toN p.inst⟩ := by
        simp only [isPreAcceptedAt, Bool.and_eq_true, beq_iff_eq] at hpo; exact hpo.1
      obtain ⟨⟨Eo, hEo⟩, hano, -, hxo, -, hoko, hrawo⟩ :=
        entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 o hor
      have hnn : o.m.status ≠ stNONE := fun h => by
        rw [h] at hpaO; revert hpaO; unfold isPA; decide
      have hvo := DecideProof.rep_reported hrr hxo hEo (Or.inl hpaO)
      rw [hvbo] at hvo
      obtain ⟨ℓo, v0o, hpho, hco⟩ := hvf.1 _ _ _ _ _ hvo hpaO
      simp only at hco
      have h2 := (hop.1 ℓo ℓe _ _ v0o v0e hpho hphe).2.1
      have hdeq' := DecideProof.depsEqual_eq (by rw [(hoko hnn).1.1, hdl]) hdeq
      have hcmd : o.m.command = e.m.command := by rw [hco, hce, h2]
      have hat := hS.2.paAttrs _ _ _ _ _ hpaO hvo
      simp only at hat
      rw [hcmd, hdeq'] at hat
      refine ⟨hano, fun h => hneq ?_, hat⟩
      simp only [InstId.mk.injEq] at hxo
      rw [DecideProof.acc_eq hrr hEo, h, hrawo, hxo.1]
    have hnd := DecideProof.reps_nodup hrr hR (l := R) (hRdef ▸ List.filter_sublist)
    have hdle : depsLe e.m.deps e.m.deps := ⟨hdl, hdl, fun _ _ => Int.le_refl _⟩
    match R, hlen, hnd, hent with
    | [], hlen, _, _ => simp [nR] at hlen
    | [_], hlen, _, _ => simp [nR] at hlen
    | o1 :: o2 :: _, _, hnd, hent =>
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
      have e1 := hent o1 (by simp)
      have e2 := hent o2 (by simp)
      refine ⟨[toN o1.m.acceptorId, toN o2.m.acceptorId, toN p.replica], ?_, by simp [fR],
        fun r hr => ?_⟩
      · simp [List.nodup_cons, hnd.1.1, e1.2.1, e2.2.1]
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨e1.1, _, e1.2.2, hdle⟩
        · exact ⟨e2.1, _, e2.2.2, hdle⟩
        · exact ⟨hxq, v0e.deps, by simp only; rw [hce]; exact hlead, hge⟩

/-- (SLOW-WIT) The accepted value is supported (`InvPM.accSup`): sub-case 2, as the reported
Accept is (`DecideProof.sup_sub2`); sub-case 3, by the two identical non-leader pre-accept votes
and the leader's own vote at the initial ballot. -/
theorem dec23_sup (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (p : PrepareReply) (hm : (S.sent fr i)[n]? = some (.prepareReply p))
    (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
    (hp : lb.preparing = true) (h4 : p.ballot = lb.lastTriedBallot)
    (h5 : lb.prepareReplies.any (fun e => e.m.acceptorId == p.acceptorId) = false)
    (h6 : ¬ (lb.prepareReplies ++ [(⟨p, false⟩ : PReply)]).length < (nR + 1) / 2)
    (h23 : (dD lb p).1 = 2 ∨ (dD lb p).1 = 3) :
    ∀ e, (dD lb p).2 = some e →
      (∃ r' b u, S.ev r' (.commit ⟨toN p.replica, toN p.inst⟩ b u)) ∨
      ∃ c0, realBal ⟨toN p.replica, toN p.inst⟩ c0 ∧ zz c0 ≤ zz lb.lastTriedBallot ∧
        S.cmdChosen ⟨toN p.replica, toN p.inst⟩ c0 e.m.command := by
  intro e he
  have hrr := inv_rr hS
  have hvf := inv_vf hS
  have hown := inv_own hS
  obtain ⟨-, -, -, -, -, -, hop, -⟩ := hS.1
  have hxq : toN p.replica < nR := (inv_wf hS).2.1 i hi _ w hw |>.2.1
  have hpm := mem_msgs_of_sent S hm
  obtain ⟨r1, r2, -, -⟩ := (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
  have hpraw : p.replica = W32 (toN p.replica) := raw_of _ r1 r2
  have heR : e ∈ dReps lb p := prepDecide_mem _ _ _ _ e he
  have hR := dec_reports S fr i n hS hi hfr p hm w lb hw hlb hp h4 h5 h6
  have hpN := hS.2.prepNoProp i hi _ w lb hw hlb hp
  obtain ⟨⟨E, hE⟩, -, -, hex, -, -, -⟩ :=
    entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e heR
  rcases prepDecide_23e (dReps lb p) (dMx lb p) (dLr lb p) p.replica e he h23 with
    ⟨-, hst⟩ | ⟨hib, hok⟩
  · exact DecideProof.sup_sub2 hS.1 (DecideProof.decAux_of (inv_reports hS)) hS.2.pm hR heR hst
  · right
    have hmx : dMx lb p = initBal ⟨toN p.replica, toN p.inst⟩ := by
      simp only [isInitialBallot, beq_iff_eq] at hib; rw [hib]; exact hpraw
    rw [hmx] at hok
    obtain ⟨hvbe, hpaE⟩ := sub3_e hok
    have hve := DecideProof.rep_reported hrr hex hE (Or.inl hpaE)
    rw [hvbe] at hve
    obtain ⟨ℓe, v0e, hphe, hce⟩ := hvf.1 _ _ _ _ _ hve hpaE
    simp only at hce
    have hℓe : ℓe = toN p.replica := by
      obtain ⟨p1, p2, -, hp1, -⟩ := hown.2.1 _ _ _ _ hphe
      rcases (hown.1 _ _ _ (List.mem_of_getElem? hp1)).1 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [zz_initBal _ hxq] at h; simp [nR] at h hxq; omega
    obtain ⟨stL, uL, hsL, hvL, hcL⟩ := (hS.2.pm.cmdSafe _ _ _ _ hphe).1
    rw [hℓe] at hvL
    simp only [subCase3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨-, hlen⟩ := hok
    obtain ⟨R, hRdef⟩ : ∃ R, R = (dReps lb p).filter (fun o =>
        isPreAcceptedAt (initBal ⟨toN p.replica, toN p.inst⟩) o &&
        o.m.acceptorId != o.m.replica && o.m.seq == e.m.seq && depsEqual o.m.deps e.m.deps) :=
      ⟨_, rfl⟩
    rw [← hRdef] at hlen
    have hent : ∀ o ∈ R, toN o.m.acceptorId < nR ∧ toN o.m.acceptorId ≠ toN p.replica ∧
        ∃ st u, (isPA st ∨ st = stACCEPTED) ∧ S.ev (toN o.m.acceptorId)
          (.vote ⟨toN p.replica, toN p.inst⟩ (initBal ⟨toN p.replica, toN p.inst⟩) st u) ∧
          u.cmds = e.m.command := by
      intro o ho
      rw [hRdef, List.mem_filter] at ho
      obtain ⟨hor, hpo⟩ := ho
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hpo
      obtain ⟨⟨⟨hpo, hneq⟩, -⟩, -⟩ := hpo
      have hpaO : isPA o.m.status := by
        simp only [isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpo
        exact hpo.2
      have hvbo : o.m.vballot = initBal ⟨toN p.replica, toN p.inst⟩ := by
        simp only [isPreAcceptedAt, Bool.and_eq_true, beq_iff_eq] at hpo; exact hpo.1
      obtain ⟨⟨Eo, hEo⟩, hano, -, hxo, -, -, hrawo⟩ :=
        entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 o hor
      have hvo := DecideProof.rep_reported hrr hxo hEo (Or.inl hpaO)
      rw [hvbo] at hvo
      obtain ⟨ℓo, v0o, hpho, hco⟩ := hvf.1 _ _ _ _ _ hvo hpaO
      simp only at hco
      have h2 := (hop.1 ℓo ℓe _ _ v0o v0e hpho hphe).2.1
      have hcmd : o.m.command = e.m.command := by rw [hco, hce, h2]
      refine ⟨hano, fun h => hneq ?_, _, _, Or.inl hpaO, hvo, hcmd⟩
      simp only [InstId.mk.injEq] at hxo
      rw [DecideProof.acc_eq hrr hEo, h, hrawo, hxo.1]
    have hnd := DecideProof.reps_nodup hrr hR (l := R) (hRdef ▸ List.filter_sublist)
    refine ⟨initBal ⟨toN p.replica, toN p.inst⟩, Or.inl rfl, ?_, ?_⟩
    · have := hpN.1; rw [zz_initBal _ hxq]; simp only [nR] at hxq this ⊢; omega
    match R, hlen, hnd, hent with
    | [], hlen, _, _ => simp [nR] at hlen
    | [_], hlen, _, _ => simp [nR] at hlen
    | o1 :: o2 :: _, _, hnd, hent =>
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
      have e1 := hent o1 (by simp)
      have e2 := hent o2 (by simp)
      refine ⟨[toN o1.m.acceptorId, toN o2.m.acceptorId, toN p.replica], ?_, by simp [nR],
        fun r hr => ?_⟩
      · simp [List.nodup_cons, hnd.1.1, e1.2.1, e2.2.1]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨e1.1, e1.2.2⟩
        · exact ⟨e2.1, e2.2.2⟩
        · exact ⟨hxq, stL, uL, Or.inl hsL, hvL, by rw [hcL, ← hce]⟩

/-- **Sub-cases 2 and 3**: the replica accepts the chosen reply's value at its ballot and
broadcasts the Accept (safe: `DecideProof.decide_safe`). -/
theorem inv_deliver_dec23 (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (p : PrepareReply) (hm : (S.sent fr i)[n]? = some (.prepareReply p))
    (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
    (hp : lb.preparing = true) (h2 : stGe w.status stCOMMITTED = false)
    (h3 : lb.lastTriedBallot.slt w.bal = false) (h4 : p.ballot = lb.lastTriedBallot)
    (h5 : lb.prepareReplies.any (fun e => e.m.acceptorId == p.acceptorId) = false)
    (h6 : ¬ (lb.prepareReplies ++ [(⟨p, false⟩ : PReply)]).length < (nR + 1) / 2)
    (h1 : ¬ (dD lb p).1 = 1) (h23 : (dD lb p).1 = 2 ∨ (dD lb p).1 = 3) :
    Inv (S.deliver fr i n (.prepareReply p)) := by
  have hpm := mem_msgs_of_sent S hm
  obtain ⟨r1, r2, r3, r4⟩ := (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
  have hpraw : p.replica = W32 (toN p.replica) := raw_of _ r1 r2
  have hxq : toN p.replica < nR := (inv_wf hS).2.1 i hi _ w hw |>.2.1
  obtain ⟨e, he, hst⟩ := prepDecide_23 _ _ _ _ h23
  have heR : e ∈ dReps lb p := prepDecide_mem _ _ _ _ e he
  obtain ⟨⟨E, hE⟩, -, -, hex, hnil, hok, -⟩ :=
    entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e heR
  have hpN := hS.2.prepNoProp i hi _ w lb hw hlb hp
  have hnn : e.m.status ≠ stNONE := by
    intro h; rw [h] at hst; rcases hst with h | h | h <;> cases h
  obtain ⟨hdeps, hcne⟩ := hok hnn
  have hcf : e.cmdsNil = false := by
    cases h : e.cmdsNil
    · rfl
    · exact absurd (hnil h) hnn
  obtain ⟨l1, l2, l3, l4⟩ := dLb_some lb p e he
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -, -, -, f11⟩ := dLb_fields lb p
  rw [hcf] at l1; simp only [Bool.false_eq_true, if_false] at l1
  have hlbI := inv_lb hS i hi _ w lb hw hlb
  -- the decision is safe
  have hR := dec_reports S fr i n hS hi hfr p hm w lb hw hlb hp h4 h5 h6
  have hnov := dec_nov S fr i n hS hi hfr p hm w lb hw hlb hp h4
  obtain ⟨hnoph, hnoacc⟩ := dec_noprop S fr i n hS hi hfr p hm w lb hw hlb hp h4
  have hdd : dD lb p = prepDecide (dReps lb p) ((dReps lb p).foldl DecideProof.maxStep (W32 (-1)))
      (dLr lb p) (W32 (toN p.replica)) := by
    unfold dD dMx; exact congrArg _ hpraw
  have hlr : dLr lb p = true → ∃ e ∈ dReps lb p, toN e.m.acceptorId = toN p.replica := by
    intro h
    simp only [dLr, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨e', he', hae⟩
    · obtain ⟨e', he', h'⟩ := hpN.2.2.2.2 h
      exact ⟨e', List.mem_append_left _ he', h'⟩
    · obtain ⟨-, -, -, hx', -⟩ := entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e' he'
      simp only [InstId.mk.injEq] at hx'
      exact ⟨e', he', by rw [hae, hx'.1]⟩
  have hlr' : dLr lb p = false → ∀ e ∈ dReps lb p, e.m.acceptorId ≠ e.m.replica := by
    intro h e' he' hae
    simp only [dLr, Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq] at h
    exact h.2 e' he' hae
  have hsafeA : S.safeAcc ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot
      ⟨e.m.command, e.m.seq, e.m.deps⟩ := by
    have := (DecideProof.decide_safe hS.1 (DecideProof.decAux_of (inv_reports hS)) hxq hpN.1 hR
      hnov (dLr lb p) hlr hlr').1
    rw [← hdd] at this
    exact this h23 e he
  -- the value is the batch or a no-op
  have hval : e.m.command = noop ∨ ∃ ps, S.owner ⟨toN p.replica, toN p.inst⟩ = some ps ∧
      e.m.command = ps.map (·.cmd) := by
    have hrr := (inv_rr hS).1 _ e.m E hE
    have hev : S.ev (toN e.m.acceptorId)
        (.vote ⟨toN p.replica, toN p.inst⟩ e.m.vballot e.m.status ⟨e.m.command, e.m.seq, e.m.deps⟩) := by
      obtain ⟨pp, pp', -, h, -⟩ := hrr.2.1 (hst.symm.imp (fun h => h) (fun h => h) |>.elim
        (fun h => Or.inl h) (fun h => Or.inr h))
      rw [← hex]; exact List.mem_of_getElem? h
    rcases hst with hs | hs
    · rw [hs] at hev
      obtain ⟨ℓ, hl⟩ := (inv_vf hS).2 _ _ _ _ hev
      exact hS.2.valOk ℓ _ _ _ (Or.inr hl)
    · obtain ⟨ℓ, v0, hph, hc⟩ := (inv_vf hS).1 _ _ _ _ _ hev hs
      have := hS.2.valOk ℓ _ _ _ (Or.inl hph)
      simp only at hc; rw [hc]; exact this
  -- the step
  have hout : hMsg (S.rep i) (.prepareReply p) =
      ((bumpRecvBallot (S.rep i) p.ballot).setInst ⟨toN p.replica, toN p.inst⟩
          (RecAcceptProof.accKnown w { dLb lb p with status := stACCEPTED } lb.lastTriedBallot
            ⟨e.m.command, e.m.seq, e.m.deps⟩),
        [Out.ev (.vote ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot stACCEPTED
            ⟨e.m.command, e.m.seq, e.m.deps⟩),
         Out.ev (.accept ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot ⟨e.m.command, e.m.seq, e.m.deps⟩),
         Out.bcast (bcastAcceptOf ((bumpRecvBallot (S.rep i) p.ballot).setInst
            ⟨toN p.replica, toN p.inst⟩
            (RecAcceptProof.accKnown w { dLb lb p with status := stACCEPTED } lb.lastTriedBallot
              ⟨e.m.command, e.m.seq, e.m.deps⟩)) ⟨toN p.replica, toN p.inst⟩
            (acceptOf ((bumpRecvBallot (S.rep i) p.ballot).setInst ⟨toN p.replica, toN p.inst⟩
              (RecAcceptProof.accKnown w { dLb lb p with status := stACCEPTED } lb.lastTriedBallot
                ⟨e.m.command, e.m.seq, e.m.deps⟩)) p.replica p.inst
              { dLb lb p with status := stACCEPTED }))]) := by
    simp only [hMsg]
    rw [dec_eq (S.rep i) p w lb hw hlb hp h2 h3 h4 h5 h6]
    unfold dOut
    rw [if_neg h1, if_pos h23]
    simp only [dInst, RecAcceptProof.accKnown, lbVal]
    generalize dLb lb p = L at l1 l2 l3 f1 ⊢
    cases L; simp only at l1 l2 l3 f1; subst l1 l2 l3 f1; rfl
  have hH := hs_deliver S fr i n (.prepareReply p) hidle hm
  rw [hout] at hH
  generalize hσ1 : (bumpRecvBallot (S.rep i) p.ballot).setInst ⟨toN p.replica, toN p.inst⟩
    (RecAcceptProof.accKnown w { dLb lb p with status := stACCEPTED } lb.lastTriedBallot
      ⟨e.m.command, e.m.seq, e.m.deps⟩) = σ1 at hH
  have hH' : HS S (S.deliver fr i n (.prepareReply p)) i σ1
      [.vote ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot stACCEPTED ⟨e.m.command, e.m.seq, e.m.deps⟩,
       .accept ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot ⟨e.m.command, e.m.seq, e.m.deps⟩]
      (fun _ => [])
      (bcastAcceptOf σ1 ⟨toN p.replica, toN p.inst⟩
        (acceptOf σ1 p.replica p.inst { dLb lb p with status := stACCEPTED })).norm := by
    have e1 : ∀ (a b : Event) (c : Bcast), evsOf [Out.ev a, Out.ev b, Out.bcast c] = [a, b] :=
      fun _ _ _ => rfl
    have e2 : ∀ (a b : Event) (c : Bcast), sendsOf [Out.ev a, Out.ev b, Out.bcast c] =
      fun _ => [] := fun _ _ _ => by funext to; rfl
    have e3 : ∀ (a b : Event) (c : Bcast), pendFold [Out.ev a, Out.ev b, Out.bcast c] none =
      c.norm := fun _ _ _ => rfl
    rw [e1, e2, e3] at hH; exact hH
  have hid : σ1.id = i := by rw [← hσ1]; simp [RState.setInst]; exact (inv_wf hS).1 i hi
  refine RecAcceptProof.inv_accept_start S _ i σ1 _ w lb { dLb lb p with status := stACCEPTED }
    lb.lastTriedBallot _ _ _ hS hi hidle hH' (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h)) ⟨rfl, rfl, by rw [← hσ1]; simp [RState.setInst, bcastAcceptOf], rfl, rfl, rfl⟩
    ⟨by simp [acceptOf, hid], rfl, r1, r2, r3, r4, by simp [acceptOf, f1],
      by simp only [acceptOf, l1, l2, l3, Option.getD_some]⟩
    (by rw [← hσ1]; simp [RState.setInst]) (by rw [← hσ1]; simp [RState.setInst])
    (by rw [← hσ1]; exact AuxProof.bumpRB_cls _ _) hw hlb
    (DecideProof.notCommitted_of_stGe h2) ((slt_false _ _).mp h3) rfl (by have := hpN.1; omega)
    hnoacc (fun r u h => absurd h (hnoph r u)) hsafeA ?_ hdeps hcne hval ?_ ?_
    (Or.inr (dec23_prop S fr i n hS hi hfr p hm w lb hw hlb hp h4 e he heR h23 hst f4))
    (by simp only [f11])
    (dec23_wit S fr i n hS hi hfr hidle p hm w lb hw hlb hp h2 h3 h4 h5 h6 h1 h23 e he)
    (dec23_sup S fr i n hS hi hfr p hm w lb hw hlb hp h4 h5 h6 h23 e he)
  · intro h
    have := hpN.1; rw [h, zz_initBal ⟨toN p.replica, toN p.inst⟩ hxq] at this; simp [nR] at this hxq; omega
  · refine ⟨f1, by simp only [f4]; exact dMx_le S fr i n hS hi hfr p hm w lb hw hlb hp h4 hpN.1,
      rfl, f3, by simp only [f5]; exact hlbI.2.2.1, f2, by simp only [l3]; exact hdeps,
      by simp only [l1], l2, l3⟩
  · obtain ⟨-, -, -, -, -, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, -, -⟩ := hlbI
    refine ⟨⟨Q, q1, by simp only [f6]; exact q2, fun a m' hq => ?_⟩,
      ⟨Q', q1', by simp only [f7]; exact q2', fun a hq => ?_⟩⟩
    · obtain ⟨b1, b2, b3, b4, b5, -⟩ := q3 a m' hq
      exact ⟨b1, b2, hH'.deliveredMsg_old b3, b4, by simp only [f1]; exact b5⟩
    · obtain ⟨b1, b2, m', b3, b4, b5⟩ := q3' a hq
      exact ⟨b1, b2, m', hH'.deliveredMsg_old b3, b4, by simp only [f1]; exact b5⟩

theorem prepDecide_5 (reps : List PReply) (mx : w32) (lr : Bool) (rep : w32) (e : PReply)
    (h1 : (prepDecide reps mx lr rep).1 ≠ 1) (h2 : (prepDecide reps mx lr rep).1 ≠ 2)
    (h3 : (prepDecide reps mx lr rep).1 ≠ 3) (he : (prepDecide reps mx lr rep).2 = some e) :
    isPA e.m.status := by
  revert h1 h2 h3 he
  unfold prepDecide
  split
  · intro h1; exact absurd rfl h1
  split
  · intro _ h2; exact absurd rfl h2
  split
  · intro _ _ h3; exact absurd rfl h3
  split
  · rename_i e' he'
    intro _ _ _ he
    simp only [Option.some.injEq] at he; subst he
    have := List.find?_some he'
    simp only [isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
    exact this.2
  · intro _ _ _ he; cases he

/-! ## Sub-cases 5 and 6 -/

/-- **Sub-cases 5 and 6**: the replica starts a Phase 1 at its ballot with the reported
pre-accepted commands or a no-op (safe: `DecideProof.decide_safe`). -/
theorem inv_deliver_dec56 (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (p : PrepareReply) (hm : (S.sent fr i)[n]? = some (.prepareReply p))
    (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w) (hlb : w.lb = some lb)
    (hp : lb.preparing = true) (h2 : stGe w.status stCOMMITTED = false)
    (h3 : lb.lastTriedBallot.slt w.bal = false) (h4 : p.ballot = lb.lastTriedBallot)
    (h5 : lb.prepareReplies.any (fun e => e.m.acceptorId == p.acceptorId) = false)
    (h6 : ¬ (lb.prepareReplies ++ [(⟨p, false⟩ : PReply)]).length < (nR + 1) / 2)
    (h1 : ¬ (dD lb p).1 = 1) (h23 : ¬ ((dD lb p).1 = 2 ∨ (dD lb p).1 = 3)) :
    Inv (S.deliver fr i n (.prepareReply p)) := by
  have hpm := mem_msgs_of_sent S hm
  obtain ⟨r1, r2, r3, r4⟩ := (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
  have hpraw : p.replica = W32 (toN p.replica) := raw_of _ r1 r2
  have hxq : toN p.replica < nR := (inv_wf hS).2.1 i hi _ w hw |>.2.1
  have hpN := hS.2.prepNoProp i hi _ w lb hw hlb hp
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -⟩ := dLb_fields lb p
  have hlbI := inv_lb hS i hi _ w lb hw hlb
  -- the decision is safe
  have hR := dec_reports S fr i n hS hi hfr p hm w lb hw hlb hp h4 h5 h6
  have hnov := dec_nov S fr i n hS hi hfr p hm w lb hw hlb hp h4
  obtain ⟨hnoph, hnoacc⟩ := dec_noprop S fr i n hS hi hfr p hm w lb hw hlb hp h4
  have hdd : dD lb p = prepDecide (dReps lb p) ((dReps lb p).foldl DecideProof.maxStep (W32 (-1)))
      (dLr lb p) (W32 (toN p.replica)) := by
    unfold dD dMx; exact congrArg _ hpraw
  have hlr : dLr lb p = true → ∃ e ∈ dReps lb p, toN e.m.acceptorId = toN p.replica := by
    intro h
    simp only [dLr, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨e', he', hae⟩
    · obtain ⟨e', he', h'⟩ := hpN.2.2.2.2 h
      exact ⟨e', List.mem_append_left _ he', h'⟩
    · obtain ⟨-, -, -, hx', -⟩ := entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e' he'
      simp only [InstId.mk.injEq] at hx'
      exact ⟨e', he', by rw [hae, hx'.1]⟩
  have hlr' : dLr lb p = false → ∀ e ∈ dReps lb p, e.m.acceptorId ≠ e.m.replica := by
    intro h e' he' hae
    simp only [dLr, Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq] at h
    exact h.2 e' he' hae
  have hsafeP : S.safePh ⟨toN p.replica, toN p.inst⟩ lb.lastTriedBallot := by
    have := (DecideProof.decide_safe hS.1 (DecideProof.decAux_of (inv_reports hS)) hxq hpN.1 hR
      hnov (dLr lb p) hlr hlr').2
    rw [← hdd] at this
    exact this h1 (fun h => h23 (Or.inl h)) (fun h => h23 (Or.inr h))
  -- the commands
  have hcmd : (dLb lb p).cmds.getD [] ≠ [] ∧ ((dLb lb p).cmds.getD [] = noop ∨
      ∃ ps, S.owner ⟨toN p.replica, toN p.inst⟩ = some ps ∧
        (dLb lb p).cmds.getD [] = ps.map (·.cmd)) := by
    cases hd2 : (dD lb p).2 with
    | none =>
      have : (dLb lb p).cmds = some noop := by unfold dLb; rw [hd2]
      rw [this]; exact ⟨by simp [noop], Or.inl rfl⟩
    | some e =>
      have heR : e ∈ dReps lb p := prepDecide_mem _ _ _ _ e hd2
      have hpa : isPA e.m.status := prepDecide_5 _ _ _ _ e h1 (fun h => h23 (Or.inl h))
        (fun h => h23 (Or.inr h)) hd2
      obtain ⟨⟨E, hE⟩, -, -, hex, hnil, hok, -⟩ :=
        entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e heR
      have hnn : e.m.status ≠ stNONE := by
        intro h; rw [h] at hpa; rcases hpa with h | h <;> cases h
      have hcf : e.cmdsNil = false := by
        cases h : e.cmdsNil
        · rfl
        · exact absurd (hnil h) hnn
      obtain ⟨l1, -, -, -⟩ := dLb_some lb p e hd2
      rw [hcf] at l1; simp only [Bool.false_eq_true, if_false] at l1
      rw [l1]
      refine ⟨(hok hnn).2, ?_⟩
      have hrr := (inv_rr hS).1 _ e.m E hE
      obtain ⟨pp, pp', -, h, -⟩ := hrr.2.1 (Or.inl hpa)
      have hev := List.mem_of_getElem? h
      rw [hex] at hev
      obtain ⟨ℓ, v0, hph, hc⟩ := (inv_vf hS).1 _ _ _ _ _ hev hpa
      have := hS.2.valOk ℓ _ _ _ (Or.inl hph)
      simp only at hc; simp only [Option.getD_some]; rw [hc]; exact this
  -- (SLOW-WIT) the Phase 1 is command-safe
  have hcmdS : ∀ c, realBal ⟨toN p.replica, toN p.inst⟩ c → zz c < zz lb.lastTriedBallot →
      ∀ Z, Z ≠ (dLb lb p).cmds.getD [] → S.cmdBlocked ⟨toN p.replica, toN p.inst⟩ c Z := by
    have hdd' : dD lb p = prepDecide (dReps lb p)
        ((dReps lb p).foldl DecideProof.maxStep (W32 (-1))) (dLr lb p) p.replica := rfl
    have hnn : (∀ e ∈ dReps lb p, stGe e.m.status stCOMMITTED = false) ∧
        (∀ e ∈ dReps lb p, ¬ (e.m.vballot = (dReps lb p).foldl DecideProof.maxStep (W32 (-1)) ∧
          e.m.status = stACCEPTED)) := by
      rcases DecideProof.prepDecide_cases (dReps lb p)
          ((dReps lb p).foldl DecideProof.maxStep (W32 (-1))) (dLr lb p) p.replica with
        h | ⟨hnc, ⟨h2', -⟩ | ⟨hna, -⟩⟩
      · rw [← hdd'] at h; exact absurd h h1
      · rw [← hdd'] at h2'; exact absurd (Or.inl h2') h23
      · exact ⟨hnc, hna⟩
    refine DecideProof.cmd_sub56 hS.1 (DecideProof.decAux_of (inv_reports hS)) hS.2.pm hxq hR hnov
      hnn.1 hnn.2 _ ?_
    rcases DecideProof.prepDecide_56 (dReps lb p) (dMx lb p) (dLr lb p) p.replica h1
        (fun h => h23 (Or.inl h)) (fun h => h23 (Or.inr h)) with ⟨-, hno⟩ | ⟨e, he, heR, hpe⟩
    · left
      intro e he hc
      have := hno e he
      rw [show isPreAcceptedAt (dMx lb p) e = true by
        simp only [isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact hc] at this
      cases this
    · right
      simp only [isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpe
      obtain ⟨⟨E, hE⟩, -, -, -, hnil, -, -⟩ :=
        entry_report S fr i n hS hi hfr p hm w lb hw hlb hp h4 e heR
      have hnn' : e.m.status ≠ stNONE := by
        intro h; rw [h] at hpe; rcases hpe.2 with h | h <;> cases h
      have hcf : e.cmdsNil = false := by
        cases h : e.cmdsNil
        · rfl
        · exact absurd (hnil h) hnn'
      obtain ⟨l1, -, -, -⟩ := dLb_some lb p e he
      rw [hcf] at l1; simp only [Bool.false_eq_true, if_false] at l1
      exact ⟨e, heR, hpe.1, hpe.2, by rw [l1]; rfl⟩
  -- the step
  have hH := hs_deliver S fr i n (.prepareReply p) hidle hm
  have hout : hMsg (S.rep i) (.prepareReply p) =
      startPhase1 ((bumpRecvBallot (S.rep i) p.ballot).setInst ⟨toN p.replica, toN p.inst⟩
          { dInst w lb p with lb := some (dLb lb p) }) ((dLb lb p).cmds.getD [])
        ⟨toN p.replica, toN p.inst⟩ p.replica p.inst (dLb lb p).lastTriedBallot
        (dLb lb p).clientProposals := by
    simp only [hMsg]
    rw [dec_eq (S.rep i) p w lb hw hlb hp h2 h3 h4 h5 h6]
    unfold dOut
    rw [if_neg h1, if_neg h23]
  rw [hout, f1] at hH
  generalize hσ0 : (bumpRecvBallot (S.rep i) p.ballot).setInst ⟨toN p.replica, toN p.inst⟩
    { dInst w lb p with lb := some (dLb lb p) } = σ0 at hH
  generalize hcm : (dLb lb p).cmds.getD [] = cmds at hH hcmd hcmdS
  have hσ0c : σ0.conflicts = (S.rep i).conflicts := by rw [← hσ0]; simp [RState.setInst]
  have hσ0i : ∀ y, y ≠ (⟨toN p.replica, toN p.inst⟩ : InstId) → σ0.inst y = (S.rep i).inst y := by
    intro y hy; rw [← hσ0]; simp [RState.setInst, upd_apply, hy]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := RecPhase1Proof.sp1_spec σ0 cmds
    ⟨toN p.replica, toN p.inst⟩ p.replica p.inst lb.lastTriedBallot (dLb lb p).clientProposals
  rw [g8] at hH
  have hH' := hH
  simp only [evsOf, sendsOf, pendFold, List.filterMap_cons, List.filterMap_nil, Out.hev,
    Out.sendTo, List.foldl_cons, List.foldl_nil] at hH'
  have hid : σ0.id = i := by rw [← hσ0]; simp [RState.setInst]; exact (inv_wf hS).1 i hi
  refine RecPhase1Proof.inv_phase1_start S _ i _ σ0 _ _ w lb
    (RecPhase1Proof.sp1Lb cmds lb.lastTriedBallot
      (updateAttributes σ0 cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 (dLb lb p).clientProposals)
    lb.lastTriedBallot p.inst cmds (updateAttributes σ0 cmds (W32 0) (List.replicate nR (W32 (-1)))).1
    (updateAttributes σ0 cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 _ _
    hS hi hidle rfl hσ0c
    ⟨by rw [← hσ0]; exact (AuxProof.bumpRB_cls _ _).1, by rw [← hσ0]; exact (AuxProof.bumpRB_cls _ _).2⟩
    hH' (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h)) ⟨rfl, rfl, by simp only [bcastPreAcceptOf]; rw [g3, ← hσ0]; simp [RState.setInst],
      rfl, rfl⟩
    ⟨by simp [preAcceptOf, g2, hid], rfl, r1, r2, r3, r4, rfl, by simp [preAcceptOf, RecPhase1Proof.sp1Lb], rfl, rfl⟩
    (by rw [g1]; funext y; simp only [upd_apply]; split
        · rfl
        · exact hσ0i y (by assumption))
    ⟨by rw [g2, ← hσ0]; simp [RState.setInst], by rw [g3, ← hσ0]; simp [RState.setInst],
      by rw [g4, ← hσ0]; simp [RState.setInst], by rw [g5, ← hσ0]; simp [RState.setInst],
      by rw [g6, ← hσ0]; simp [RState.setInst]⟩
    ⟨by simp [RState.setInst, hσ0c], g7⟩
    ⟨by rw [← hσ0]; exact (AuxProof.bumpRB_cls _ _).1, by rw [← hσ0]; exact (AuxProof.bumpRB_cls _ _).2,
      by rw [g1]; rfl, (RecPhase1Proof.sp1_cls _ _ _ _ _ _ _).1, (RecPhase1Proof.sp1_cls _ _ _ _ _ _ _).2⟩
    ⟨r3, rfl⟩ hw hlb
    (DecideProof.notCommitted_of_stGe h2) ((slt_false _ _).mp h3) rfl hpN.1 hnoph hnoacc hnov
    hsafeP hcmdS hcmd.1 hcmd.2 ⟨rfl, rfl, rfl, rfl, rfl, by simp [RecPhase1Proof.sp1Lb, f2], rfl, rfl,
      rfl, rfl⟩

end DecideStepProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
