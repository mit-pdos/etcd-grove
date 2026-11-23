/-
`handleCommit` (`hCommit`): the law `inv_deliver_commit`. A Commit for an instance not yet
committed (and not stale) makes the record COMMITTED with the Commit's value (already decided: the
Commit message is in `committedVal`), records it in the conflicts map, and may re-propose the
leader's client proposals (dropping them from `lb`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HLocal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Conf

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace CommitProof

open HStepProof HLocal SafeProof

/-! ## `updateConflicts`, `updateCommitted` -/

theorem uc_fields (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) :
    (updateConflicts σ cmds q n seq).inst = σ.inst ∧ (updateConflicts σ cmds q n seq).id = σ.id ∧
    (updateConflicts σ cmds q n seq).peerOrder = σ.peerOrder ∧
    (updateConflicts σ cmds q n seq).crtInstance = σ.crtInstance ∧
    (updateConflicts σ cmds q n seq).execedUpTo = σ.execedUpTo ∧
    (updateConflicts σ cmds q n seq).store = σ.store := by
  unfold updateConflicts
  induction cmds generalizing σ with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons c cs ih => rw [List.foldl_cons]; exact ih _

/-- Every conflicts entry satisfies `G` after `updateConflicts` if it did before and `G` holds of
the new instance number (and of `-1`). -/
theorem uc_conf (σ : RState) (cmds : List WCmd) (q0 : Nat) (n seq : w32) (G : Nat → w32 → Prop)
    (hG : ∀ q k p, σ.conflicts q k = some p → G q p.last ∧ G q p.lastWrite)
    (hn : G q0 n) (hm1 : G q0 (W32 (-1))) :
    ∀ q k p, (updateConflicts σ cmds q0 n seq).conflicts q k = some p →
      G q p.last ∧ G q p.lastWrite := by
  unfold updateConflicts
  induction cmds generalizing σ with
  | nil => exact hG
  | cons c cs ih =>
    rw [List.foldl_cons]
    apply ih
    intro q k p h
    simp only [upd_apply] at h
    by_cases hq : q = q0
    · subst hq; rw [if_pos rfl] at h
      by_cases hk : k = c.key
      · rw [upd_apply, if_pos hk] at h; simp only [Option.some.injEq] at h; subst h
        cases hp0 : σ.conflicts q c.key with
        | none =>
          simp only
          refine ⟨hn, ?_⟩
          split
          · exact hn
          · exact hm1
        | some p0 =>
          simp only
          obtain ⟨g1, g2⟩ := hG _ _ _ hp0
          constructor
          · split
            · exact hn
            · exact g1
          · split
            · exact hn
            · exact g2
      · rw [upd_apply, if_neg hk] at h; exact hG _ _ _ h
    · rw [if_neg hq] at h; exact hG _ _ _ h

@[simp] theorem updateCommitted_inst (σ : RState) (q : Nat) : (updateCommitted σ q).inst = σ.inst := rfl
@[simp] theorem updateCommitted_conf (σ : RState) (q : Nat) :
    (updateCommitted σ q).conflicts = σ.conflicts := rfl

/-- The record `hCommit` writes (its bookkeeping possibly without the client proposals). -/
def comRec (w : InstRec) (lbo : Option LbRec) (p : Commit) : InstRec :=
  { w with lb := lbo, bal := p.ballot, vbal := p.ballot, cmds := some p.command, seq := p.seq,
           deps := p.deps, status := stCOMMITTED }

/-- `commit_cases` with the class arrays (stage 2): kept in the first case, `updateConflicts`'
in the second (over a state with the instance set and the class arrays of `S.rep i`). -/
theorem commit_cases_cls (S : Sys) (fr i n : Nat) (p : Commit) (hidle : S.idle i)
    (hm : (S.sent fr i)[n]? = some (.commit p)) :
    ∃ σ' E, HS S (S.deliver fr i n (.commit p)) i σ' E (fun _ => []) none ∧
      σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (bumpCrt (S.rep i) (toN p.replica) p.inst).crtInstance ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store ∧
      ((σ'.inst = upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩
          (some (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩)) ∧ E = [] ∧
          σ'.conflicts = (S.rep i).conflicts ∧
          σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ lbo, (lbo = (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩).lb ∨
          ∃ lb, (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩).lb = some lb ∧
            lbo = some { lb with clientProposals := none }) ∧
        σ'.inst = upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩
          (some (comRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) lbo p)) ∧
        stGe (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩).status stCOMMITTED = false ∧
        zz (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩).bal ≤ zz p.ballot ∧
        E = [.record ⟨toN p.replica, toN p.inst⟩ p.command,
             .commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
        ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
          σ'.conflicts = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).conflicts ∧
          σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧ σb.inst = σ'.inst ∧
          σ'.lastScan = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).lastScan ∧
          σ'.lastPut = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).lastPut)) := by
  have hH := hs_deliver S fr i n (.commit p) hidle hm
  simp only [hMsg] at hH
  generalize hw0 : recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩ = w0
  have hr : recOr (bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot)
      ⟨toN p.replica, toN p.inst⟩ = w0 := by rw [← hw0]; simp [recOr]
  unfold hCommit at hH
  simp only [getOrDefault_eq, hr] at hH
  have hinst : ∀ w, ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w).inst =
      upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ (some w) := by
    intro w; simp [RState.setInst]
  have hfl : ∀ w, ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w).id = (S.rep i).id ∧
      ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w).peerOrder = (S.rep i).peerOrder ∧
      ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w).crtInstance = (bumpCrt (S.rep i) (toN p.replica) p.inst).crtInstance ∧
      ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w).execedUpTo = (S.rep i).execedUpTo ∧
      ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w).store = (S.rep i).store ∧
      ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w).conflicts = (S.rep i).conflicts := by
    intro w; simp [RState.setInst]
  have hcl0 : ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w0).lastScan = (S.rep i).lastScan ∧
      ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
      ⟨toN p.replica, toN p.inst⟩ w0).lastPut = (S.rep i).lastPut := by
    simp only [RState.setInst]
    rw [(AuxProof.bumpRB_cls _ _).1, (AuxProof.bumpCrt_cls _ _ _).1,
      (AuxProof.bumpRB_cls _ _).2, (AuxProof.bumpCrt_cls _ _ _).2]
    exact ⟨rfl, rfl⟩
  by_cases c1 : stGe w0.status stCOMMITTED = true
  · simp only [c1, if_true] at hH
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hfl w0
    simp only [evsOf, pendFold, List.filterMap_nil, List.foldl_nil] at hH
    exact ⟨_, _, hH, f1, f2, f3, f4, f5, Or.inl ⟨hinst w0, rfl, f6, hcl0.1, hcl0.2⟩⟩
  · simp only [c1, if_false, Bool.false_eq_true] at hH
    by_cases c2 : p.ballot.slt w0.bal = true
    · simp only [c2, if_true] at hH
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hfl w0
      simp only [evsOf, pendFold, List.filterMap_nil, List.foldl_nil] at hH
      exact ⟨_, _, hH, f1, f2, f3, f4, f5, Or.inl ⟨hinst w0, rfl, f6, hcl0.1, hcl0.2⟩⟩
    · simp only [c2, if_false, Bool.false_eq_true] at hH
      have hle : zz w0.bal ≤ zz p.ballot := (slt_false _ _).mp (by simpa using c2)
      have hc1 : stGe w0.status stCOMMITTED = false := by simpa using c1
      have key : ∀ (X : InstRec) (rp : List Out), (X.lb = w0.lb ∨ ∃ lb, w0.lb = some lb ∧
          X.lb = some { lb with clientProposals := none }) → X.id = w0.id →
          (∀ o ∈ rp, ∃ q, o = .repropose q) →
          HS S (S.deliver fr i n (.commit p)) i
            (updateCommitted (updateConflicts
              (((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
                ⟨toN p.replica, toN p.inst⟩ w0).setInst ⟨toN p.replica, toN p.inst⟩
                { cmds := some p.command, bal := p.ballot, vbal := p.ballot, status := stCOMMITTED,
                  seq := p.seq, deps := p.deps, lb := X.lb, id := X.id })
              p.command (toN p.replica) p.inst p.seq) (toN p.replica))
            (evsOf (rp ++ [Out.ev (.record ⟨toN p.replica, toN p.inst⟩ p.command),
              Out.ev (.commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩)]))
            (sendsOf (rp ++ [Out.ev (.record ⟨toN p.replica, toN p.inst⟩ p.command),
              Out.ev (.commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩)]))
            (pendFold (rp ++ [Out.ev (.record ⟨toN p.replica, toN p.inst⟩ p.command),
              Out.ev (.commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩)]) none) →
          ∃ σ' E, HS S (S.deliver fr i n (.commit p)) i σ' E (fun _ => []) none ∧
            σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
            σ'.crtInstance = (bumpCrt (S.rep i) (toN p.replica) p.inst).crtInstance ∧
            σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store ∧
            ((σ'.inst = upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ (some w0) ∧ E = [] ∧
                σ'.conflicts = (S.rep i).conflicts ∧
                σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
             (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
              σ'.inst = upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ (some (comRec w0 lbo p)) ∧
              stGe w0.status stCOMMITTED = false ∧ zz w0.bal ≤ zz p.ballot ∧
              E = [.record ⟨toN p.replica, toN p.inst⟩ p.command,
                   .commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
              ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
                σ'.conflicts = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).conflicts ∧
                σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
                σb.inst = σ'.inst ∧
                σ'.lastScan = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).lastScan ∧
                σ'.lastPut = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).lastPut))
              := by
        intro X rp hX hXid hrp hH'
        have he : evsOf (rp ++ [Out.ev (.record ⟨toN p.replica, toN p.inst⟩ p.command),
            Out.ev (.commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩)]) =
            [.record ⟨toN p.replica, toN p.inst⟩ p.command,
             .commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩] := by
          have hr0 : List.filterMap Out.hev rp = [] := by
            simp only [List.filterMap_eq_nil_iff]
            intro o ho; obtain ⟨q, rfl⟩ := hrp o ho; rfl
          simp only [evsOf, List.filterMap_append, hr0, List.nil_append]; rfl
        have hs : sendsOf (rp ++ [Out.ev (.record ⟨toN p.replica, toN p.inst⟩ p.command),
            Out.ev (.commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩)]) =
            fun _ => [] := by
          funext to
          simp only [sendsOf, List.filterMap_append, List.filterMap_eq_nil_iff]
          have : List.filterMap (Out.sendTo to) rp = [] := by
            simp only [List.filterMap_eq_nil_iff]
            intro o ho; obtain ⟨q, rfl⟩ := hrp o ho; rfl
          rw [this]; rfl
        have hp' : pendFold (rp ++ [Out.ev (.record ⟨toN p.replica, toN p.inst⟩ p.command),
            Out.ev (.commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩)]) none =
            none := by
          have : ∀ (l : List Out) (a : Option Bcast), (∀ o ∈ l, ∃ q, o = .repropose q) →
              pendFold l a = a := by
            intro l
            induction l with
            | nil => intro a _; rfl
            | cons o l ih =>
              intro a hl
              obtain ⟨q, rfl⟩ := hl o List.mem_cons_self
              exact ih a (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho'))
          simp only [pendFold, List.foldl_append] at this ⊢
          rw [this rp none hrp]; rfl
        rw [he, hs, hp'] at hH'
        refine ⟨_, _, hH', by simp [updateCommitted, RState.setInst, (uc_fields _ _ _ _ _).2.1],
          by simp [updateCommitted, RState.setInst, (uc_fields _ _ _ _ _).2.2.1],
          by simp [updateCommitted, RState.setInst, (uc_fields _ _ _ _ _).2.2.2.1],
          by simp [updateCommitted, RState.setInst, (uc_fields _ _ _ _ _).2.2.2.2.1],
          by simp [updateCommitted, RState.setInst, (uc_fields _ _ _ _ _).2.2.2.2.2],
          Or.inr ⟨X.lb, hX, ?_, hc1, hle, rfl, ?_⟩⟩
        · simp only [updateCommitted_inst, (uc_fields _ _ _ _ _).1, RState.setInst, upd_upd_same,
            bumpRB_inst, bumpCrt_inst]
          congr 2; simp only [comRec]; rw [← hXid]
        · refine ⟨_, by simp [RState.setInst], rfl, ?_, ?_, (ConfProof.uc_inst _ _ _ _ _).symm, rfl, rfl⟩
          · simp only [RState.setInst]
            rw [(AuxProof.bumpRB_cls _ _).1, (AuxProof.bumpCrt_cls _ _ _).1]
          · simp only [RState.setInst]
            rw [(AuxProof.bumpRB_cls _ _).2, (AuxProof.bumpCrt_cls _ _ _).2]
      by_cases c3 : toN p.replica = (S.rep i).id ∧ p.command.length = 1 ∧
          Option.map (fun x => x.op) p.command.head? = some opNONE
      · have c3' : toN p.replica =
            ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
              ⟨toN p.replica, toN p.inst⟩ w0).id ∧ p.command.length = 1 ∧
            Option.map (fun x => x.op) p.command.head? = some opNONE := by
          simpa [RState.setInst] using c3
        rw [if_pos c3'] at hH
        by_cases hl : w0.lb = none
        · simp only [hl] at hH
          first
            | exact key w0 [] (Or.inl rfl) rfl (by simp) hH
            | exact key { w0 with lb := none } [] (Or.inl hl.symm) rfl (by simp) hH
        · obtain ⟨lb, hl⟩ : ∃ lb, w0.lb = some lb := Option.ne_none_iff_exists'.mp hl
          simp only [hl] at hH
          by_cases hcp : lb.clientProposals = none
          · simp only [hcp] at hH
            first
              | exact key w0 [] (Or.inl rfl) rfl (by simp) hH
              | exact key { w0 with lb := some lb } [] (Or.inl hl.symm) rfl (by simp) hH
          · obtain ⟨ps, hcp⟩ : ∃ ps, lb.clientProposals = some ps :=
              Option.ne_none_iff_exists'.mp hcp
            simp only [hcp] at hH
            exact key { w0 with lb := some { lb with clientProposals := none } } _
              (Or.inr ⟨lb, hl, rfl⟩) rfl (by simp) hH
      · have c3' : ¬ (toN p.replica =
            ((bumpRecvBallot (bumpCrt (S.rep i) (toN p.replica) p.inst) p.ballot).setInst
              ⟨toN p.replica, toN p.inst⟩ w0).id ∧ p.command.length = 1 ∧
            Option.map (fun x => x.op) p.command.head? = some opNONE) := by
          simpa [RState.setInst] using c3
        rw [if_neg c3'] at hH
        exact key w0 [] (Or.inl rfl) rfl (by simp) hH

/-- The two cases of `hCommit` as a handler step. -/
theorem commit_cases (S : Sys) (fr i n : Nat) (p : Commit) (hidle : S.idle i)
    (hm : (S.sent fr i)[n]? = some (.commit p)) :
    ∃ σ' E, HS S (S.deliver fr i n (.commit p)) i σ' E (fun _ => []) none ∧
      σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (bumpCrt (S.rep i) (toN p.replica) p.inst).crtInstance ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store ∧
      ((σ'.inst = upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩
          (some (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩)) ∧ E = [] ∧
          σ'.conflicts = (S.rep i).conflicts) ∨
       (∃ lbo, (lbo = (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩).lb ∨
          ∃ lb, (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩).lb = some lb ∧
            lbo = some { lb with clientProposals := none }) ∧
        σ'.inst = upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩
          (some (comRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) lbo p)) ∧
        stGe (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩).status stCOMMITTED = false ∧
        zz (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩).bal ≤ zz p.ballot ∧
        E = [.record ⟨toN p.replica, toN p.inst⟩ p.command,
             .commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
        ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
          σ'.conflicts = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).conflicts)) := by
  obtain ⟨σ', E, hH, a1, a2, a3, a4, a5, h⟩ := commit_cases_cls S fr i n p hidle hm
  refine ⟨σ', E, hH, a1, a2, a3, a4, a5, ?_⟩
  rcases h with ⟨b1, b2, b3, -⟩ | ⟨lbo, b1, b2, b3, b4, b5, σb, c1, c2, -⟩
  · exact Or.inl ⟨b1, b2, b3⟩
  · exact Or.inr ⟨lbo, b1, b2, b3, b4, b5, σb, c1, c2⟩

/-! ## The step's context -/

section
variable (S S' : Sys) (fr i n : Nat) (p : Commit) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.commit p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E (fun _ => []) none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
    (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
      w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
      E = [.record x p.command, .commit x p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
      ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
        σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

theorem ctx_basic :
    Msg.commit p ∈ S.msgs fr i ∧ x.q < nR ∧ x.i + 1 < MAX_INSTANCE ∧ 0 ≤ zz p.inst ∧
    (x.i : Int) = zz p.inst ∧ fr ≠ i ∧ depsOk p.deps ∧ 0 ≤ zz p.ballot ∧
    S.committedVal x ⟨p.command, p.seq, p.deps⟩ := by
  have hpm : Msg.commit p ∈ S.msgs fr i := mem_msgs_of_sent S hm
  obtain ⟨r1, r2, r3, r4⟩ := (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
  have hdeps := (hS.1.2.1 fr i _ hpm).2 p.deps (by simp [Msg.depsFields])
  refine ⟨hpm, ?_, ?_, r3, ?_, (hS.1.1.2.2.2.2.2.1 fr i (List.ne_nil_of_mem hpm)).2.2, hdeps,
    hS.2.commitBal fr i p hpm, Or.inr ⟨fr, i, p, hpm, by rw [hx]; rfl, rfl⟩⟩
  · subst hx; simp only [toN, zz] at r1 r2 ⊢; omega
  · subst hx; exact r4
  · subst hx; exact toN_of_zz _ r3

theorem ctx_rec : (∀ r y w, (S'.rep r).inst y = some w →
      (r = i ∧ y = x ∧ w = w') ∨ (S.rep r).inst y = some w) ∧
    (∀ r y w, (S.rep r).inst y = some w →
      (r = i ∧ y = x ∧ w = w0) ∨ (S'.rep r).inst y = some w) ∧
    (S'.rep i).inst x = some w' ∧
    (∀ r y, (r ≠ i ∨ y ≠ x) → (S'.rep r).inst y = (S.rep r).inst y) := by
  have hr : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some w' else (S.rep r).inst y := by
    intro r y
    rw [hH.rep]
    by_cases h : r = i
    · subst h; simp only [upd_same, hσi, upd_apply, true_and]
    · simp [upd_other _ _ _ _ h, h]
  refine ⟨fun r y w h => ?_, fun r y w h => ?_, by rw [hr]; simp, fun r y h => ?_⟩
  · rw [hr] at h; split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; simp only [Option.some.injEq] at h
      exact Or.inl ⟨rfl, rfl, h.symm⟩
    · exact Or.inr h
  · by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc
      rcases hro with h' | ⟨h', -⟩
      · rw [h'] at h; simp only [Option.some.injEq] at h; exact Or.inl ⟨rfl, rfl, h.symm⟩
      · rw [h'] at h; cases h
    · right; rw [hr, if_neg hc]; exact h
  · rw [hr, if_neg (by rintro ⟨rfl, rfl⟩; rcases h with h | h <;> exact h rfl)]

theorem ctx_fields : ∀ r, (S'.rep r).id = (S.rep r).id ∧
    (S'.rep r).peerOrder = (S.rep r).peerOrder ∧ (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧
    (S'.rep r).store = (S.rep r).store ∧
    (∀ q, zz ((S'.rep r).crtInstance q) =
      if r = i ∧ q = x.q then max (zz ((S.rep r).crtInstance q)) (zz p.inst)
      else zz ((S.rep r).crtInstance q)) := by
  intro r
  rw [hH.rep]
  by_cases h : r = i
  · subst h; simp only [upd_same]
    refine ⟨hid, hpo, hexe, hsto, fun q => ?_⟩
    rw [hcrt, zz_bumpCrt]
    by_cases hq : q = x.q
    · subst hq; simp
    · simp [hq]
  · simp [h]

/-- The record `w'` against `w0`. -/
theorem ctx_w : zz w0.bal ≤ zz w'.bal ∧ w'.id = w0.id ∧ zz w'.vbal ≤ zz w'.bal ∧
    (∀ lb', w'.lb = some lb' → ∃ lb, w0.lb = some lb ∧
      (lb' = lb ∨ lb' = { lb with clientProposals := none })) ∧
    (∀ lb, w0.lb = some lb → ∃ lb', w'.lb = some lb' ∧ (lb' = lb ∨
      lb' = { lb with clientProposals := none })) ∧
    (w' = w0 ∨ (isCommitted w'.status ∧ w'.vbal = p.ballot ∧ w'.bal = p.ballot ∧
      instVal w' = ⟨p.command, p.seq, p.deps⟩ ∧ w'.cmds = some p.command ∧ w'.deps = p.deps ∧
      ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot)) ∧
    (w0.status = stNONE ∨ isPA w0.status ∨ w0.status = stACCEPTED ∨ isCommitted w0.status) ∧
    zz w0.vbal ≤ zz w0.bal ∧ w0.id = x := by
  have h0 : (w0.status = stNONE ∨ isPA w0.status ∨ w0.status = stACCEPTED ∨
      isCommitted w0.status) ∧ zz w0.vbal ≤ zz w0.bal ∧ w0.id = x := by
    rcases hro with h | ⟨-, rfl⟩
    · exact ⟨hS.2.stRange i hi x w0 h, hS.1.2.2.2.2.1.1 i hi x w0 h, (hS.1.1.2.1 i hi x w0 h).1⟩
    · exact ⟨Or.inl rfl, by simp [newInstanceDefault], rfl⟩
  rcases hcase with ⟨he, -⟩ | ⟨lbo, hlbo, he, h3, h4, -⟩
  · subst w'
    exact ⟨Int.le_refl _, rfl, h0.2.1, fun lb' h => ⟨lb', h, Or.inl rfl⟩,
      fun lb h => ⟨lb, h, Or.inl rfl⟩, Or.inl rfl, h0⟩
  · subst w'
    refine ⟨h4, rfl, Int.le_refl _, fun lb' h => ?_, fun lb h => ?_,
      Or.inr ⟨Or.inl rfl, rfl, rfl, by simp [comRec, instVal], rfl, rfl, h3, h4⟩, h0⟩
    · simp only [comRec] at h
      rcases hlbo with rfl | ⟨lb, h1, rfl⟩
      · exact ⟨lb', h, Or.inl rfl⟩
      · simp only [Option.some.injEq] at h; exact ⟨lb, h1, Or.inr h.symm⟩
    · simp only [comRec]
      rcases hlbo with rfl | ⟨lb0, h1, rfl⟩
      · exact ⟨lb, h, Or.inl rfl⟩
      · rw [h] at h1; cases h1; exact ⟨_, rfl, Or.inr rfl⟩

theorem ctx_ev : ∀ r e, S'.ev r e → S.ev r e ∨ (r = i ∧
    (e = .record x p.command ∨ e = .commit x p.ballot ⟨p.command, p.seq, p.deps⟩)) := by
  intro r e he
  rcases (hH.ev_iff r e).mp he with h | ⟨hr, h⟩
  · exact Or.inl h
  · right; refine ⟨hr, ?_⟩
    rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, -, -, -, rfl, -⟩
    · cases h
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h; exact h

theorem ctx_ev_old (r : Nat) (e : Event) (he : S'.ev r e) (h1 : e ≠ .record x p.command)
    (h2 : e ≠ .commit x p.ballot ⟨p.command, p.seq, p.deps⟩) : S.ev r e := by
  rcases ctx_ev S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r e he with h | ⟨-, h | h⟩
  · exact h
  · exact absurd h h1
  · exact absurd h h2

theorem ctx_notE (e : Event) (h1 : e ≠ .record x p.command)
    (h2 : e ≠ .commit x p.ballot ⟨p.command, p.seq, p.deps⟩) : i = i → e ∉ E := by
  intro _ he
  rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, -, -, -, rfl, -⟩
  · cases he
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with h | h
    · exact h1 h
    · exact h2 h

theorem ctx_msgs : ∀ fr' to m, m ∈ S'.msgs fr' to ↔ m ∈ S.msgs fr' to := by
  intro fr' to m
  rw [hH.mem_msgs]
  constructor
  · rintro (h | ⟨-, h | h⟩)
    · exact h
    · cases h
    · simp [intendedOf] at h
  · exact Or.inl

theorem ctx_cv : ∀ y v, S'.committedVal y v ↔ S.committedVal y v := by
  obtain ⟨-, -, -, -, -, -, -, -, hcv⟩ := ctx_basic S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro y v
  constructor
  · rintro (⟨r, b, h⟩ | ⟨fr', to, m, hm', hy, rfl⟩)
    · rcases ctx_ev S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ h with h' | ⟨-, h' | h'⟩
      · exact Or.inl ⟨r, b, h'⟩
      · cases h'
      · simp only [Event.commit.injEq] at h'; obtain ⟨rfl, -, rfl⟩ := h'; exact hcv
    · exact Or.inr ⟨fr', to, m, (ctx_msgs S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to _).mp hm', hy, rfl⟩
  · rintro (⟨r, b, h⟩ | ⟨fr', to, m, hm', hy, rfl⟩)
    · exact Or.inl ⟨r, b, hH.ev_old h⟩
    · exact Or.inr ⟨fr', to, m, hH.msgs_old hm', hy, rfl⟩

theorem ctx_prep : ∀ r m e, S'.prepReport r m e → S.prepReport r m e ∧ (r = i → e ∉ E) := by
  rintro r m e ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
  · exact ⟨⟨ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he (fun h => by cases h) (fun h => by cases h),
      Or.inl ⟨to, (ctx_msgs S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r to _).mp hm', rfl⟩⟩,
      fun _ => ctx_notE S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (fun h => by cases h) (fun h => by cases h) rfl⟩
  · exact ⟨⟨ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he (fun h => by cases h) (fun h => by cases h), Or.inr rfl⟩,
      fun _ => ctx_notE S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (fun h => by cases h) (fun h => by cases h) rfl⟩

theorem ctx_vote_old : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v) :=
  fun r y b st v h => ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ h (fun h => by cases h) (fun h => by cases h)

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Commit) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.commit p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E (fun _ => []) none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
    (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
      w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
      E = [.record x p.command, .commit x p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
      ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
        σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

theorem ctx_wf : Inv.wf S' := by
  obtain ⟨hpm, hxq, hxi, hpi0, hpi, hfi, hdeps, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have F := ctx_fields S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, hid', -, hlb1, -, hw', hst0, -, hid0⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hS.1.1
  have hA := hS.2
  have hlbx : x.q = i → w0.lb ≠ none := by
    intro hq
    rcases hro with h | ⟨h, rfl⟩
    · exact (w2 i hi x w0 h).2.2.2.2.2.1 hq
    · exfalso
      have hc := hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)
      rw [← hq] at h
      obtain ⟨w, lb, hw, -⟩ := hA.ownRow x.q hxq x.i hc
      rw [show (⟨x.q, x.i⟩ : InstId) = x from rfl, h] at hw; cases hw
  refine ⟨fun r hr => by rw [(F r).1]; exact w1 r hr, fun r hr y w hw => ?_,
    fun r hr q hq => ?_, fun r hr q k p0 hk => ?_, fun r hr q hq m' hm' => ?_,
    fun fr' to hne => ?_, fun fr' to n' hn' => ?_, fun r b hb => ?_⟩
  · rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w
      have hw0 : (S.rep i).inst x = some w0 ∨ w0 = newInstanceDefault x := by
        rcases hro with h | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
      refine ⟨hid' ▸ hid0, hxq, hxi, fun hs => ?_, fun lb hlb hs => ?_, fun hq hn' => ?_,
        fun lb ps hlb hps => ?_⟩
      · rcases hw' with he | ⟨-, -, -, -, -, hd, -⟩
        · subst he
          rcases hw0 with h | h
          · exact (w2 i hi x w' h).2.2.2.1 hs
          · rw [h] at hs; exact absurd rfl hs
        · rw [hd]; exact hdeps
      · obtain ⟨lb0, hlb0, he⟩ := hlb1 lb hlb
        have hsd : lb.status = lb0.status ∧ lb.deps = lb0.deps := by
          rcases he with he | he <;> rw [he] <;> exact ⟨rfl, rfl⟩
        rw [hsd.2]; rw [hsd.1] at hs
        rcases hw0 with h | h
        · exact (w2 i hi x w0 h).2.2.2.2.1 lb0 hlb0 hs
        · rw [h] at hlb0; cases hlb0
      · obtain ⟨lb0, hlb0⟩ := Option.ne_none_iff_exists'.mp (hlbx hq)
        obtain ⟨lb', hlb', -⟩ := hS.2.makerLb i x (W32 0) hi |> fun _ => (ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn).2.2.2.2.1 lb0 hlb0
        rw [hn'] at hlb'; cases hlb'
      · rw [hH.owner]
        obtain ⟨lb0, hlb0, he⟩ := hlb1 lb hlb
        rcases he with he | he
        · rw [he] at hps
          rcases hw0 with h | h
          · exact (w2 i hi x w0 h).2.2.2.2.2.2 lb0 ps hlb0 hps
          · rw [h] at hlb0; cases hlb0
        · rw [he] at hps; simp at hps
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2 r hr y w h
      exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
  · have e := (F r).2.2.2.2 q
    obtain ⟨c1, c2⟩ := w3 r hr q hq
    simp only [toN, zz] at e c1 c2 hxi hpi hpi0 ⊢
    rw [e]
    split
    · constructor <;> omega
    · exact ⟨c1, c2⟩
  · -- the conflicts map: the old entries and the new instance exist
    have G : ∀ q k p0, (S.rep r).conflicts q k = some p0 →
        (q < nR ∧ (0 ≤ zz p0.last → (S'.rep r).inst ⟨q, toN p0.last⟩ ≠ none)) ∧
        (q < nR ∧ (0 ≤ zz p0.lastWrite → (S'.rep r).inst ⟨q, toN p0.lastWrite⟩ ≠ none)) := by
      intro q k p0 hk
      obtain ⟨k1, k2, k3⟩ := w4 r hr q k p0 hk
      have hk' : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
        intro y hy hn'
        cases h' : (S.rep r).inst y with
        | none => exact hy h'
        | some w =>
          rcases R2 r y w h' with ⟨hr', hy', -⟩ | h''
          · subst hr'; rw [hy'] at hn'; rw [R3] at hn'; cases hn'
          · rw [h''] at hn'; cases hn'
      exact ⟨⟨k1, fun h => hk' _ (k2 h)⟩, ⟨k1, fun h => hk' _ (k3 h)⟩⟩
    by_cases hri : r = i
    · subst r
      rw [hH.rep_self] at hk ⊢
      rcases hcase with ⟨-, -, hc⟩ | ⟨-, -, -, -, -, -, σb, hσb, hc⟩
      · rw [hc] at hk
        have := G q k p0 hk
        rw [hH.rep_self] at this
        exact ⟨this.1.1, this.1.2, this.2.2⟩
      · rw [hc] at hk
        have := uc_conf σb p.command x.q p.inst p.seq
          (fun q v => q < nR ∧ (0 ≤ zz v → σ'.inst ⟨q, toN v⟩ ≠ none))
          (by intro q k p0 h; rw [hσb] at h; have := G q k p0 h; rw [hH.rep_self] at this; exact this)
          ⟨hxq, fun _ => by rw [hσi]; simp [upd_apply, hx, hpi0]⟩
          ⟨hxq, fun h => by simp [zz] at h⟩ q k p0 hk
        exact ⟨this.1.1, this.1.2, this.2.2⟩
    · rw [hH.rep_other hri] at hk
      have := G q k p0 hk
      exact ⟨this.1.1, this.1.2, this.2.2⟩
  · rw [(F r).2.2.1] at hm'
    obtain ⟨w, hw, hs⟩ := w5 r hr q hq m' hm'
    rcases R2 r _ w hw with ⟨hr', hy, hw''⟩ | h''
    · subst hr' hw''
      refine ⟨w', by rw [hy]; exact R3, ?_⟩
      rcases hw' with he | ⟨-, -, -, -, -, -, hnc, -⟩
      · rw [he]; exact hs
      · exact absurd (Or.inr hs) hnc
    · exact ⟨w, h'', hs⟩
  · rw [hH.msgs] at hne
    by_cases h0 : S.msgs fr' to = []
    · rw [h0, List.nil_append] at hne
      split at hne
      · simp [intendedOf] at hne
      · exact absurd rfl hne
    · exact w6 fr' to h0
  · rcases hH.delOk fr' to n' hn' with h | h
    · rw [hH.sent]; exact w7 fr' to n' h
    · rw [hH.sent]; exact h
  · rw [hH.pending] at hb
    by_cases hr : r = i
    · subst hr; simp at hb
    · rw [upd_other _ _ _ _ hr] at hb
      obtain ⟨d1, d2, d3, d4, d5, d6, w, lb, hw, hlb⟩ := w8 r b hb
      refine ⟨d1, by rw [hH.execCur]; exact d2, d3, d4, d5, d6, w, lb, ?_, hlb⟩
      rw [R4 r _ (Or.inl hr)]; exact hw

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Commit) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.commit p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E (fun _ => []) none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
    (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
      w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
      E = [.record x p.command, .commit x p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
      ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
        σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

theorem ctx_simple : Inv.msgWf S' ∧ Inv.replyTargets S' ∧ Inv.noTPA S' ∧ Inv.ballotOwner S' ∧
    Inv.oneProposal S' ∧ Inv.votesFollowProposals S' ∧ Inv.commitMsgs S' ∧ Inv.pendingKind S' := by
  have hmsg := ctx_msgs S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, -, -, hlb1, hlb2, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun fr' to m hm' => hS.1.2.1 fr' to m ((hmsg _ _ _).mp hm'), fun fr' to m y hm' hy hk => ?_,
    fun fr' to m hm' => hS.1.2.2.2.1 fr' to m ((hmsg _ _ _).mp hm'), ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, lb, hw, hlb⟩ := hS.1.2.2.1 fr' to m y ((hmsg _ _ _).mp hm') hy hk
    rcases R2 to y w hw with ⟨h1, h2, h3⟩ | h'
    · subst to y w
      obtain ⟨lb', hlb', -⟩ := hlb2 lb hlb
      exact ⟨w', lb', R3, hlb'⟩
    · exact ⟨w, lb, h', hlb⟩
  · obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hS.1.2.2.2.2.2.1
    refine ⟨fun r y b he => ?_, fun r y b v he => ?_, fun r y b v he => ?_, fun r to m hm' => ?_,
      fun r to m hm' => ?_, fun r to m hm' => ?_⟩
    · have h := hold r _ he (fun h => by cases h) (fun h => by cases h)
      refine ⟨(o1 r y b h).1, ?_⟩
      by_cases hr : r = i
      · rw [hH.count_eq (fun _ => ctx_notE S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (fun h => by cases h) (fun h => by cases h) rfl)]
        exact (o1 r y b h).2
      · rw [hH.count_eq (fun h => absurd h hr)]; exact (o1 r y b h).2
    · exact hH.evBefore_old (o2 r y b v (hold r _ he (fun h => by cases h) (fun h => by cases h)))
    · exact hH.ev_old (o3 r y b v (hold r _ he (fun h => by cases h) (fun h => by cases h)))
    · obtain ⟨c1, c2⟩ := o4 r to m ((hmsg _ _ _).mp hm'); exact ⟨c1, hH.ev_old c2⟩
    · obtain ⟨c1, c2⟩ := o5 r to m ((hmsg _ _ _).mp hm'); exact ⟨c1, hH.ev_old c2⟩
    · obtain ⟨c1, c2⟩ := o6 r to m ((hmsg _ _ _).mp hm'); exact ⟨c1, hH.ev_old c2⟩
  · obtain ⟨p1, p2, p3⟩ := hS.1.2.2.2.2.2.2.1
    refine ⟨fun r r' y b v v' he he' => ?_, fun r r' y b v v' he he' => ?_,
      fun r r' y b v v' he he' => ?_⟩
    · have h := hold r _ he (fun h => by cases h) (fun h => by cases h)
      have h' := hold r' _ he' (fun h => by cases h) (fun h => by cases h)
      obtain ⟨c1, c2, c3⟩ := p1 r r' y b v v' h h'
      refine ⟨c1, c2, ?_⟩
      by_cases hr : r = i
      · rw [hH.count_eq (fun _ => ctx_notE S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (fun h => by cases h) (fun h => by cases h) rfl)]
        exact c3
      · rw [hH.count_eq (fun h => absurd h hr)]; exact c3
    · exact p2 r r' y b v v' (hold r _ he (fun h => by cases h) (fun h => by cases h))
        (hold r' _ he' (fun h => by cases h) (fun h => by cases h))
    · exact p3 r r' y b v v' (hold r _ he (fun h => by cases h) (fun h => by cases h))
        (hold r' _ he' (fun h => by cases h) (fun h => by cases h))
  · obtain ⟨v1, v2⟩ := hS.1.2.2.2.2.2.2.2.1
    refine ⟨fun r y b st v he hst => ?_, fun r y b v he => ?_⟩
    · obtain ⟨l, v0, h1, h2⟩ := v1 r y b st v (ctx_vote_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b st v he) hst
      exact ⟨l, v0, hH.ev_old h1, h2⟩
    · obtain ⟨l, h1⟩ := v2 r y b v (ctx_vote_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b _ v he); exact ⟨l, hH.ev_old h1⟩
  · intro fr' to m hm'
    obtain ⟨r, b, h1⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 fr' to m
      ((hmsg _ _ _).mp hm')
    exact ⟨r, b, hH.ev_old h1⟩
  · intro r b hb
    rw [hH.pending] at hb
    by_cases hri : r = i
    · subst r; simp at hb
    · rw [upd_other _ _ _ _ hri] at hb
      exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r b hb

theorem ctx_ballots : Inv.ballots S' := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, -, hvb, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r hr y w hw => ?_, fun r hr y b st v he => ?_⟩
  · rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w; exact hvb
    · exact hS.1.2.2.2.2.1.1 r hr y w h
  · obtain ⟨w, hw, hle⟩ := hS.1.2.2.2.2.1.2 r hr y b st v (ctx_vote_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b st v he)
    rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h'
    · subst r y w; exact ⟨w', R3, Int.le_trans hle hwb⟩
    · exact ⟨w, h', hle⟩

theorem ctx_rr : Inv.repliesReportVotes S' ∧ Inv.prepReplyHighest S' := by
  obtain ⟨q1, q2, q3⟩ := hS.1.2.2.2.2.2.2.2.2.1
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hvo := ctx_vote_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hmsg := ctx_msgs S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hvoE : ∀ r y b st v, r = i → Event.vote y b st v ∉ E := fun r y b st v _ =>
    ctx_notE S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (fun h => by cases h) (fun h => by cases h) rfl
  refine ⟨⟨fun r m e hp => ?_, fun a r m hm' => ?_, fun a r m hm' => ?_⟩, fun r m e hp b st v hb => ?_⟩
  · obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r m e hp
    obtain ⟨c1, c2, c3, c4, c5⟩ := q1 r m e hp0
    refine ⟨c1, fun hs => hH.evBefore_old (c2 hs), fun hs => (hcv _ _).mpr (c3 hs),
      fun hs b st v hb => c4 hs b st v (hH.evBefore_back hb hp0.1 hne),
      fun b st v hb => c5 b st v (hH.evBefore_back hb (hvo _ _ _ _ _ (by
        obtain ⟨pp, pp', -, -, h⟩ := hb; exact List.mem_of_getElem? h)) (hvoE r _ _ _ _))⟩
  · obtain ⟨c1, c2, c3, c4⟩ := q2 a r m ((hmsg _ _ _).mp hm')
    refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
    · obtain ⟨v, hv⟩ := c1; exact ⟨v, hH.ev_old hv⟩
    · obtain ⟨d1, v, d2, d3⟩ := c2 hs; exact ⟨d1, v, hH.ev_old d2, d3⟩
    · obtain ⟨v, d2, d3⟩ := c3 hs; exact ⟨v, hH.ev_old d2, d3⟩
    · obtain ⟨v, d2, d3⟩ := c4 hs; exact ⟨v, (hcv _ _).mpr d2, d3⟩
  · rcases q3 a r m ((hmsg _ _ _).mp hm') with ⟨v, hv⟩ | ⟨⟨b, v, hv⟩, c2⟩
    · exact Or.inl ⟨v, hH.evBefore_old hv⟩
    · refine Or.inr ⟨⟨b, v, hH.evBefore_old hv⟩, fun m' e' hp hy hb => ?_⟩
      obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn a m' e' hp
      have hsent : S.ev a (.sent r (.acceptReply m)) := by
        obtain ⟨pp, pp', -, -, h1⟩ := hv; exact List.mem_of_getElem? h1
      exact c2 m' e' hp0 hy (hH.evBefore_back hb hsent
        (fun _ => ctx_notE S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (fun h => by cases h) (fun h => by cases h) rfl))
  · obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r m e hp
    exact hS.1.2.2.2.2.2.2.2.2.2.1 r m e hp0 b st v (hH.evBefore_back hb hp0.1 hne)

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Commit) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.commit p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E (fun _ => []) none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
    (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
      w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
      E = [.record x p.command, .commit x p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
      ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
        σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

/-- The record at `(i, x)`: old, a fresh default, or the new committed one. -/
theorem ctx_rel : ∀ r y w, (S'.rep r).inst y = some w →
    (S.rep r).inst y = some w ∨
    (r = i ∧ y = x ∧ (S.rep i).inst x = none ∧ w = newInstanceDefault x) ∨
    (r = i ∧ y = x ∧ w = w' ∧ isCommitted w'.status ∧
      w'.vbal = p.ballot ∧ w'.bal = p.ballot ∧ instVal w' = ⟨p.command, p.seq, p.deps⟩ ∧
      w'.cmds = some p.command ∧ w'.deps = p.deps ∧ ¬ isCommitted w0.status ∧
      zz w0.bal ≤ zz p.ballot) := by
  obtain ⟨R1, -⟩ := ctx_rec S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, -, -, -, -, hw', -⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro r y w hw
  rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
  · subst h3
    rcases hw' with he | h
    · rw [he]; rcases hro with h' | ⟨h', h0⟩
      · rw [h1, h2]; exact Or.inl h'
      · exact Or.inr (Or.inl ⟨h1, h2, h', h0⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, rfl, h⟩)
  · exact Or.inl h

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Commit) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.commit p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E (fun _ => []) none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
    (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
      w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
      E = [.record x p.command, .commit x p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
      ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
        σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

/-- A bookkeeping after the step is an old one, up to `clientProposals`. -/
theorem ctx_lbold : ∀ r y w lb, (S'.rep r).inst y = some w → w.lb = some lb →
    ∃ w0' lb0, (S.rep r).inst y = some w0' ∧ w0'.lb = some lb0 ∧
      (lb = lb0 ∨ lb = { lb0 with clientProposals := none }) ∧
      (w0' = w ∨ (r = i ∧ y = x ∧ w = w' ∧ isCommitted w'.status ∧ zz w0'.bal ≤ zz w'.bal)) := by
  obtain ⟨-, -, -, hlb1, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro r y w lb hw hlb
  rcases ctx_rel S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w hw with h | ⟨-, -, -, rfl⟩ | ⟨h1, h2, h3, hc, -, hb, -, -, -, -, hle⟩
  · exact ⟨w, lb, h, hlb, Or.inl rfl, Or.inl rfl⟩
  · simp [newInstanceDefault] at hlb
  · subst h3
    obtain ⟨lb0, hlb0, he⟩ := hlb1 lb hlb
    rcases hro with h' | ⟨-, h'⟩
    · refine ⟨w0, lb0, by rw [h1, h2]; exact h', hlb0, he, Or.inr ⟨h1, h2, rfl, hc, ?_⟩⟩
      rw [hb]; exact hle
    · rw [h'] at hlb0; simp [newInstanceDefault] at hlb0

theorem ctx_lb : Inv.lbInv S' := by
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro r hr y w lb hw hlb
  obtain ⟨w0', lb0, hw0', hlb0, he, hrel⟩ := ctx_lbold S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w lb hw hlb
  obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
    hS.1.2.2.2.2.2.2.2.2.2.2.1 r hr y w0' lb0 hw0' hlb0
  have key : lb.lastTriedBallot = lb0.lastTriedBallot ∧ lb.ballot = lb0.ballot ∧
      lb.tryingToPreAccept = lb0.tryingToPreAccept ∧ lb.status = lb0.status ∧
      lb.preAcceptOKs = lb0.preAcceptOKs ∧ lb.preparing = lb0.preparing ∧ lb.cmds = lb0.cmds ∧
      lb.deps = lb0.deps ∧ lb.seq = lb0.seq ∧ lb.allEqual = lb0.allEqual ∧
      lb.acceptOKs = lb0.acceptOKs ∧ lb.prepareReplies = lb0.prepareReplies := by
    rcases he with he | he <;> rw [he] <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ := key
  rw [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12]
  refine ⟨hH.ev_old a1, a2, a3, fun b v hv => a4 b v ?_, fun c1 c2 => ?_, ⟨Q, q1, q2, ?_⟩,
    ⟨Q', q1', q2', ?_⟩, fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
  · rcases hv with hv | hv
    · exact Or.inl (hold r _ hv (fun h => by cases h) (fun h => by cases h))
    · exact Or.inr (hold r _ hv (fun h => by cases h) (fun h => by cases h))
  · obtain ⟨d1, d2, v, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, v, hH.ev_old d3, d4⟩
  · intro a m' h; obtain ⟨b1, b2, b3, b4⟩ := q3 a m' h; exact ⟨b1, b2, hH.deliveredMsg_old b3, b4⟩
  · intro a h; obtain ⟨b1, b2, m', b3, b4⟩ := q3' a h
    exact ⟨b1, b2, m', hH.deliveredMsg_old b3, b4⟩
  · rcases hrel with rfl | ⟨-, -, rfl, hc, -⟩
    · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
    · rw [c2] at hc; exact absurd hc acc_not_comm
  · obtain ⟨c1, c2⟩ := a9 hp
    refine ⟨c1, fun e he => ?_⟩
    obtain ⟨d1, d2, d3⟩ := c2 e he
    refine ⟨d1, d2, ?_⟩
    rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, hH.deliveredMsg_old e2⟩
    · exact Or.inr ⟨e1, hH.ev_old e2⟩

theorem ctx_agr : Inv.agreement S' ∧ Inv.decidedChosen S' ∧ Inv.depsCover S' ∧
    Inv.witnesses S' ∧ Inv.attrsCover S' ∧ Inv.slots S' ∧ Inv.clientOps S' := by
  obtain ⟨-, -, -, -, -, -, -, -, hcvp⟩ := ctx_basic S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨⟨fun y v v' h h' => hS.1.2.2.2.2.2.2.2.2.2.2.2.1.1 y v v' ((hcv _ _).mp h)
    ((hcv _ _).mp h'), fun r hr y w hw hc => ?_⟩, fun y v hv => ?_, fun y z vy vz hyz hy hz hi' => ?_,
    fun y v hv hn' => ?_, fun r e y cy z cz d hrec hyz hb hint => ?_, ?_, ?_⟩
  · rcases ctx_rel S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w hw with h | ⟨-, -, -, rfl⟩ | ⟨h1, h2, rfl, -, -, -, hv, hcm, -⟩
    · obtain ⟨c1, c2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 r hr y w h hc
      exact ⟨c1, (hcv _ _).mpr c2⟩
    · simp [newInstanceDefault] at hc; exact absurd hc none_not_comm
    · rw [h2, hv, hcm]; exact ⟨by simp, (hcv _ _).mpr hcvp⟩
  · rcases hS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 y v ((hcv _ _).mp hv) with ⟨b, Q, h1, h2, h3⟩ |
      ⟨⟨Q, h1, h2, h3⟩, hf⟩
    · exact Or.inl ⟨b, Q, h1, h2, fun r hr => ⟨(h3 r hr).1, hH.ev_old (h3 r hr).2⟩⟩
    · refine Or.inr ⟨⟨Q, h1, h2, fun r hr => ?_⟩, hH.ev_old hf⟩
      obtain ⟨c1, c2, st, c3, c4⟩ := h3 r hr
      exact ⟨c1, c2, st, c3, hH.ev_old c4⟩
  · exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y z vy vz hyz ((hcv _ _).mp hy) ((hcv _ _).mp hz) hi'
  · obtain ⟨W, w1, w2, w3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y v ((hcv _ _).mp hv) hn'
    exact ⟨W, w1, w2, fun r hr => by
      obtain ⟨c1, d, c2, c3⟩ := w3 r hr; exact ⟨c1, d, hH.ev_old c2, c3⟩⟩
  · have h2 := hold r _ (by obtain ⟨p1, p2, -, -, h⟩ := hb; exact List.mem_of_getElem? h)
      (fun h => by cases h) (fun h => by cases h)
    exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r e y cy z cz d hrec hyz
      (hH.evBefore_back hb h2 (fun _ => ctx_notE S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (fun h => by cases h) (fun h => by cases h) rfl))
      hint
  · obtain ⟨s1, s2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨fun y v hv => ?_, fun y ps h => ?_⟩
    · rw [hH.owner]; exact s1 y v ((hcv _ _).mp hv)
    · rw [hH.owner] at h; rw [hH.ops]; exact s2 y ps h
  · have hso : S'.slotOp = S.slotOp := by funext sl; simp only [Sys.slotOp, hH.owner]
    have := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [Inv.clientOps, hso, hH.gexec, hH.fired, hH.ops, hcv] at this ⊢
    exact this

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Commit) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.commit p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E (fun _ => []) none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
    (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
      w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
      E = [.record x p.command, .commit x p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
      ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
        σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

/-- An executed record is unchanged, before and after. -/
theorem ctx_exe_same : ∀ r y, ((S.rep r).executed y ∨ (S'.rep r).executed y) →
    (S'.rep r).inst y = (S.rep r).inst y := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, -, -, -, -, hw', -⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro r y h
  by_cases hc : r = i ∧ y = x
  · obtain ⟨rfl, rfl⟩ := hc
    rw [R3]
    rcases h with ⟨w, hw, hs⟩ | ⟨w, hw, hs⟩
    · rcases hro with h' | ⟨h', -⟩
      · rw [h'] at hw ⊢; cases hw
        rcases hw' with he | ⟨-, -, -, -, -, -, hnc, -⟩
        · rw [he]
        · exact absurd (Or.inr hs) hnc
      · rw [h'] at hw; cases hw
    · rw [R3] at hw; cases hw
      rcases hcase with ⟨he, -⟩ | ⟨lbo, -, he, -⟩
      · rcases hro with h' | ⟨-, h0⟩
        · rw [h', he]
        · exfalso; rw [he, h0] at hs; simp [newInstanceDefault, stNONE, stEXECUTED] at hs
      · exfalso; rw [he] at hs; simp [comRec, stCOMMITTED, stEXECUTED] at hs
  · exact R4 r y (by
      by_cases h1 : r = i
      · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
      · exact Or.inl h1)

theorem ctx_exec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧ Inv.execPrefix S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hsame := ctx_exe_same S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hex : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
    intro r y
    constructor
    · intro h; have := hsame r y (Or.inr h); obtain ⟨w, hw, hs⟩ := h; rw [this] at hw; exact ⟨w, hw, hs⟩
    · intro h; have := hsame r y (Or.inl h); obtain ⟨w, hw, hs⟩ := h; rw [← this] at hw; exact ⟨w, hw, hs⟩
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr
    refine ⟨by rw [hH.execLog]; exact e1, fun y => by rw [hH.execLog, hex]; exact e2 y,
      fun y w hw hs => ?_⟩
    have he := hsame r y (Or.inr ⟨w, hw, hs⟩)
    rw [he] at hw
    obtain ⟨c1, c2⟩ := e3 y w hw hs
    refine ⟨(hcv _ _).mpr c1, fun z hz => ?_⟩
    obtain ⟨w2, hw2, hz1, hz2⟩ := hz
    rw [he, hw] at hw2; cases hw2
    rw [hex, hH.execCur]; exact c2 z ⟨w, hw, hz1, hz2⟩
  · by_cases hri : r = i
    · subst r
      have hc0 : S.execCur i = [] := hidle.2
      have hi0 := (hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hr).1 hc0
      rw [hH.execCur, hH.execIdx]
      exact ⟨fun _ => hi0, fun h => absurd hc0 h⟩
    · have := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr
      rw [hH.rep_other hri, hH.execCur, hH.execIdx]; exact this
  · have hdE : S'.dEdge = S.dEdge := by funext y z; simp only [Sys.dEdge, hcv]
    have hsO : S'.sccOrd = S.sccOrd := by funext y z; simp only [Sys.sccOrd, hcv]
    intro r hr i0 j y z hij hy hz ht
    rw [hH.execLog] at hy hz; rw [hdE, hsO] at *
    exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr i0 j y z hij hy hz ht
  · have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
      intro r k
      by_cases hri : r = i
      · subst r
        have hc0 : S.execCur i = [] := hidle.2
        simp only [Sys.lexec, Sys.curSlots, hH.execCur, hc0, hH.execLog, List.append_nil]
        refine slotsOn_congr _ _ _ k (fun y hy => ?_)
        exact hsame i y (Or.inl (((hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi).2.1 y).mp hy))
      · simp only [Sys.lexec, Sys.curSlots, hH.execCur, hH.execLog, hH.execIdx, hH.rep_other hri]
    obtain ⟨p1, p2, p3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
    · rw [hlx, hH.gexec]; exact p1 r hr k
    · rw [hlx, (ctx_fields S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r).2.2.2.1]; exact p2 r hr k
    · rw [hlx] at h; rw [hH.gexec]; exact p3 r hr k pre e post h

theorem ctx_mono : SafeMono S S' := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, -, -, -, -, hw', -⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r y w hw => ?_, fun r e he => hH.ev_old he,
    fun r y b st v he => Or.inl (ctx_vote_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b st v he),
    fun y v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ _ he (fun h => by cases h) (fun h => by cases h)),
    fun a y m hm' _ _ => Or.inl ((ctx_msgs S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ _ _).mp hm')⟩
  rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
  · subst r y w
    refine ⟨w', R3, hwb, fun hs => Or.inl ?_⟩
    rcases hw' with he | ⟨hc, -⟩
    · rw [he]; exact hs
    · exact comm_stGeAcc hc
  · exact ⟨w, h, Int.le_refl _, fun hs => Or.inl hs⟩

theorem ctx_safe : Inv.safe S' :=
  safe_step (ctx_mono S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn) hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun r y b v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he (fun h => by cases h) (fun h => by cases h)))
    (fun r y b v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he (fun h => by cases h) (fun h => by cases h)))

theorem ctx_reports : Inv.reports S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrepo⟩ :=
    hS.1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hrepo
  have hmo := ctx_mono S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hP := ctx_prep S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hvo := ctx_vote_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r m e hp => c1 r m e (hP r m e hp).1, fun r m e hp => c2 r m e (hP r m e hp).1,
    fun r m e hp => c3 r m e (hP r m e hp).1, fun r m e hp b u hb => ?_, fun r m e hr hp => ?_,
    fun r y b st st' v v' h1 h2 h3 h4 => c6 r y b st st' v v' h1 h2 (hvo _ _ _ _ _ h3)
      (hvo _ _ _ _ _ h4), fun y v m e h1 h2 h3 => c7 y v m e
      (ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ _ h1 (fun h => by cases h) (fun h => by cases h)) (hP _ m e h2).1 h3,
    fun r y v h1 w => fastBlocked_mono hmo
      (c8 r y v (ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ h1 (fun h => by cases h) (fun h => by cases h)) w),
    fun r m e hp => c9 r m e (hP r m e hp).1⟩
  · obtain ⟨hp0, hne⟩ := hP r m e hp
    exact c4 r m e hp0 b u (hH.evBefore_back hb hp0.1 hne)
  · obtain ⟨w, hw, hle⟩ := c5 r m e hr (hP r m e hp).1
    obtain ⟨w', hw', hle', -⟩ := hmo.bal r _ w hw
    exact ⟨w', hw', Int.le_trans hle hle'⟩

end

/-- Under a handler step with no pending broadcast and no direct sends, what is sent or in an
outbox after it was sent or in an outbox before. -/
private theorem sob_hs {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    (hH : HS S S' i σ' E (fun _ => []) none) (hp : S.pending i = none)
    (fr to : Nat) (m : Msg) (h : m ∈ S'.sent fr to ++ S'.outbox fr to) :
    m ∈ S.sent fr to ++ S.outbox fr to := by
  have hI : S'.intended fr to = S.intended fr to := by
    unfold Sys.intended; rw [hH.pending]
    by_cases hf : fr = i
    · subst hf; simp [upd_same, hp]
    · simp [upd_other _ _ _ _ hf]
  have hm := hH.msgs fr to
  simp only [Sys.msgs, hI, hH.sent, intendedOf, List.append_nil, ite_self, List.append_nil] at hm
  rw [hH.sent] at h
  rw [List.append_cancel_right hm] at h
  exact h

section
variable (S S' : Sys) (fr i n : Nat) (p : Commit) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.commit p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E (fun _ => []) none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
    (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
      w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
      E = [.record x p.command, .commit x p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
      ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
        σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

/-- `InvPM` after `handleCommit`. -/
theorem ctx_pm : InvPM S' := by
  obtain ⟨hpm, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, R2, R3, -⟩ := ctx_rec S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hP := hS.2.pm
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hvo := ctx_vote_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hmsg := ctx_msgs S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
  have hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v) :=
    fun r y b v h => hold r _ h (fun h => by cases h) (fun h => by cases h)
  have hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v) :=
    fun r y b v h => hold r _ h (fun h => by cases h) (fun h => by cases h)
  have hsent : ∀ fr' to m, m ∈ S.sent fr' to → m ∈ S'.sent fr' to :=
    fun _ _ _ h => by rw [hH.sent]; exact h
  have hcv : ∀ y u, S.committedVal y u → S'.committedVal y u :=
    fun y u h => (ctx_cv S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn y u).mpr h
  have hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w.bal ≤ zz w2.bal := by
    intro r y w h
    rcases R2 r y w h with ⟨rfl, rfl, rfl⟩ | h'
    · exact ⟨w', R3, hwb⟩
    · exact ⟨w, h', Int.le_refl _⟩
  have hlb0 : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      ∃ w1 lb1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb1 ∧ PMProof.LbPM lb1 lb2 ∧
        lb2.preAcceptsSent = lb1.preAcceptsSent := by
    intro r y w2 lb2 h hl
    obtain ⟨w1, lb1, h1, h2, h3, -⟩ := ctx_lbold S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w2 lb2 h hl
    rcases h3 with rfl | rfl
    · exact ⟨w1, lb2, h1, h2, PMProof.LbPM.refl _, rfl⟩
    · exact ⟨w1, lb1, h1, h2, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  have hlb : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      ∃ w1 lb1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb1 ∧ PMProof.LbPM lb1 lb2 := by
    intro r y w2 lb2 h hl
    obtain ⟨w1, lb1, h1, h2, h3, -⟩ := hlb0 r y w2 lb2 h hl
    exact ⟨w1, lb1, h1, h2, h3⟩
  have hpend : ∀ r b, S'.pending r = some b → S.pending r = some b := by
    intro r b h
    rw [hH.pending] at h
    by_cases hr : r = i
    · subst hr; simp at h
    · rw [upd_other _ _ _ _ hr] at h; exact h
  exact {
    arOk := PMProof.arOk_frame hP (fun a r m h => (hmsg _ _ _).mp h) hacc
      (fun q y b v h => Or.inl (hvo _ _ _ _ _ h)) hmono hcv hbal
    commitProp := by
      intro r y c u he hle
      rcases ctx_ev S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he with h | ⟨-, h | h⟩
      · exact PMProof.propAt_mono hmono (hP.commitProp r y c u h hle)
      · cases h
      · simp only [Event.commit.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        have := PMProof.propAt_mono hmono (hP.commitMsgProp fr i p hpm)
        rw [← hx] at this; exact this
    commitMsgProp := PMProof.commitMsgProp_frame hP (fun fr' to m h => (hmsg _ _ _).mp h) hmono
    lbProp := PMProof.lbProp_frame hP hlb hacc hmono
    parCom := PMProof.parCom_frame hP (fun a r m h => (hmsg _ _ _).mp h) hmono
    parSt := PMProof.parSt_frame hP (fun a r m h => (hmsg _ _ _).mp h) hsent
    paFresh := PMProof.paFresh_frame hP hlb hph
    paCmds := PMProof.paCmds_frame hP hlb hph
    paSent := PMProof.ps_frame hP
      (fun y w2 lb2 h hl => by
        obtain ⟨w1, lb1, h1, h2, h3, h4⟩ := hlb0 _ y w2 lb2 h hl
        exact ⟨w1, lb1, h1, h2, h3.1, h4⟩)
      (fun r b h _ => hpend r b h)
      (fun y a h => by
        obtain ⟨m, hm1, hm2⟩ := List.any_eq_true.mp h
        exact List.any_eq_true.mpr ⟨m, sob_hs hH hidle.1 _ _ m hm1, hm2⟩)
    pendPA := fun r b hb y c hc => hP.pendPA r b (hpend r b hb) y c hc
    paVoteMsg := PMProof.paVoteMsg_frame hP hvo hsent
    parNoPA := PMProof.parNoPA_frame hP (fun a r m h => (hmsg _ _ _).mp h) hvo
    aeF := PMProof.aeF_frame hP hlb hsent
    repLead := PMProof.repLead_frame hP (fun r m e h => (ctx_prep S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r m e h).1) hbal
    paGe := PMProof.paGe_frame hP hvo hph
    phAttrs := PMProof.phAttrs_frame hP hph hmono
    accWit := PMProof.accWit_frame hP hacc hmono hcv
    accVote := PMProof.accVote_frame hP hacc hmono
    cmdSafe := CmdSafeProof.cmdSafe_frame hP (ctx_mono S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn) hph
    accSup := CmdSafeProof.accSup_frame hP hmono hacc }

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Commit) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.commit p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E (fun _ => []) none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
    (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
      w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
      E = [.record x p.command, .commit x p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
      ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
        σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

theorem ctx_aux (hX : InvExec S')
    (hcls : (σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut ∧ E = []) ∨
      ∃ σb : RState, σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
        σb.inst = σ'.inst ∧
        σ'.lastScan = (updateConflicts σb p.command x.q p.inst p.seq).lastScan ∧
        σ'.lastPut = (updateConflicts σb p.command x.q p.inst p.seq).lastPut) :
    InvAux S' := by
  obtain ⟨hpm, hxq, hxi, hpi0, hpi, hfi, hdeps, hb0, hcvp⟩ := ctx_basic S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, hid', hvb, hlb1, hlb2, hw', hst0, hvb0, hid0⟩ := ctx_w S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hA := hS.2
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hvo := ctx_vote_old S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have F := ctx_fields S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hrel := ctx_rel S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hmsg := ctx_msgs S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hcrt' : ∀ r q, zz ((S.rep r).crtInstance q) ≤ zz ((S'.rep r).crtInstance q) := by
    intro r q; rw [(F r).2.2.2.2 q]; split <;> omega
  have hcq : ∀ q, zz ((S'.rep q).crtInstance q) = zz ((S.rep q).crtInstance q) := by
    intro q
    rw [(F q).2.2.2.2 q]
    split
    · rename_i hc; obtain ⟨rfl, hq⟩ := hc
      have := hA.crtMsg fr q _ x hpm (by rw [hx]; rfl)
      rw [← hq] at this; rw [← hpi] at *; omega
    · rfl
  -- votes of `i` for `x` before the step are at most `w0.bal`
  have hv0 : ∀ b st v, S.ev i (.vote x b st v) → (S.rep i).inst x = some w0 ∧ zz b ≤ zz w0.bal := by
    intro b st v hv
    obtain ⟨w, hw, hle⟩ := hS.1.2.2.2.2.1.2 i hi x b st v hv
    rcases hro with h | ⟨h, -⟩
    · rw [h] at hw; cases hw; exact ⟨h, hle⟩
    · rw [h] at hw; cases hw
  have hcnt0 : ∀ fr' to (P : Msg → Bool), S'.cnt fr' to P = S.cnt fr' to P := by
    intro fr' to P
    rw [hH.cnt_eq]; split
    · simp [intendedOf]
    · rfl
  have hnoP : ∀ (P : Msg → Bool) to m, m ∈ ([] : List Msg) ++ intendedOf none to → P m = false := by
    intro P to m h; simp [intendedOf] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hX⟩
  · intro r hr y w hw
    rcases hrel r y w hw with h | ⟨-, -, -, rfl⟩ | ⟨-, -, h3, hc, -⟩
    · exact hA.stRange r hr y w h
    · exact Or.inl rfl
    · subst h3; exact Or.inr (Or.inr (Or.inr hc))
  · intro r hr y w hw hs
    rcases hrel r y w hw with h | ⟨-, -, -, rfl⟩ | ⟨-, -, h3, -, -, -, -, hcm, -⟩
    · exact hA.cmdsSome r hr y w h hs
    · exact absurd rfl hs
    · subst h3; rw [hcm]; simp
  · intro r hr y w hw hs
    rcases hrel r y w hw with h | ⟨h1, h2, h3, rfl⟩ | ⟨-, -, h3, hc, -⟩
    · obtain ⟨c1, c2⟩ := hA.noneRec r hr y w h hs
      exact ⟨c1, fun b st v h' => c2 b st v (hvo _ _ _ _ _ h')⟩
    · refine ⟨by simp [newInstanceDefault], fun b st v h' => ?_⟩
      subst h1 h2
      obtain ⟨h4, -⟩ := hv0 b st v (hvo _ _ _ _ _ h'); rw [h3] at h4; cases h4
    · subst h3; rw [hs] at hc; exact absurd hc none_not_comm
  · intro r hr y w hw hs
    rcases hrel r y w hw with h | ⟨-, -, -, rfl⟩ | ⟨-, -, h3, -, hv, -⟩
    · exact hA.vbalNonneg r hr y w h hs
    · exact absurd rfl hs
    · subst h3; rw [hv]; exact hb0
  · intro r hr y w hw b st v h'
    have h'' := hvo _ _ _ _ _ h'
    rcases hrel r y w hw with h | ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, h3, -, hv, -, -, -, -, -, hle⟩
    · exact hA.votesLe r hr y w h b st v h''
    · subst h1 h2; obtain ⟨h4, -⟩ := hv0 b st v h''; rw [h3] at h4; cases h4
    · subst h1 h2; subst h3; rw [hv]
      exact Int.le_trans (hv0 b st v h'').2 hle
  · intro r hr y w hw hs
    rcases hrel r y w hw with h | ⟨-, -, -, rfl⟩ | ⟨-, -, h3, hc, -⟩
    · exact hH.ev_old (hA.recVote r hr y w h hs)
    · simp [newInstanceDefault, isPA, stNONE, stPREACCEPTED, stPREACCEPTED_EQ, stACCEPTED] at hs
    · subst h3; exfalso
      rcases hs with hs | hs
      · exact comm_not_pa hc hs
      · rw [hs] at hc; exact acc_not_comm hc
  · intro r hr y w hw b u h' hle
    have h'' := hvo _ _ _ _ _ h'
    rcases hrel r y w hw with h | ⟨h1, h2, h3, rfl⟩ | ⟨-, -, h3, hc, -⟩
    · exact hA.accKeep r hr y w h b u h'' hle
    · subst h1 h2; obtain ⟨h4, -⟩ := hv0 b _ u h''; rw [h3] at h4; cases h4
    · subst h3; exact Or.inr hc
  · intro r hr y w hw hs
    rcases hrel r y w hw with h | ⟨-, -, -, rfl⟩ | ⟨h1, h2, h3, -, -, hb, -, -, -, hnc, -⟩
    · obtain ⟨b, v, c1, c2⟩ := hA.recCommit r hr y w h hs
      exact ⟨b, v, hH.ev_old c1, c2⟩
    · exact absurd hs none_not_comm
    · subst h1 h2; subst w
      refine ⟨p.ballot, ⟨p.command, p.seq, p.deps⟩, hH.ev_new ?_, by rw [hb]; exact Int.le_refl _⟩
      rcases hcase with ⟨he, -⟩ | ⟨-, -, -, -, -, hE, -⟩
      · exfalso; rw [he] at hs; exact hnc hs
      · rw [hE]; simp
  · intro r y b v hr he
    rcases ctx_ev S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he with h | ⟨hr', h | h⟩
    · obtain ⟨w, hw, hs⟩ := hA.commitRec r y b v hr h
      rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h'
      · subst h1 h2 h3
        refine ⟨w', R3, ?_⟩
        rcases hw' with he' | ⟨hc, -⟩
        · rw [he']; exact hs
        · exact hc
      · exact ⟨w, h', hs⟩
    · cases h
    · simp only [Event.commit.injEq] at h; obtain ⟨hy, -, -⟩ := h
      subst hr' hy
      refine ⟨w', R3, ?_⟩
      rcases hcase with ⟨hw0, hE, -⟩ | ⟨lbo, -, he', -⟩
      · rcases (hH.ev_iff _ _).mp he with h0 | ⟨-, h0⟩
        · obtain ⟨w, hw, hs⟩ := hA.commitRec _ _ b v hr h0
          rcases hro with h' | ⟨h', -⟩
          · rw [h'] at hw; cases hw; rw [hw0]; exact hs
          · rw [h'] at hw; cases hw
        · rw [hE] at h0; cases h0
      · rw [he']; exact Or.inl rfl
  · intro r y v he
    obtain ⟨h1, b, h2⟩ := hA.fastCommitEv r y v (hold r _ he (fun h => by cases h) (fun h => by cases h))
    exact ⟨h1, b, hH.ev_old h2⟩
  · intro r y b hr he
    obtain ⟨w, lb, hw, hlb, hle⟩ := hA.makerLb r y b hr (hold r _ he (fun h => by cases h) (fun h => by cases h))
    rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst h1 h2 h3
      obtain ⟨lb', hlb', he'⟩ := hlb2 lb hlb
      refine ⟨w', lb', R3, hlb', ?_⟩
      rcases he' with he' | he' <;> rw [he'] <;> exact hle
    · exact ⟨w, lb, h, hlb, hle⟩
  · intro r hr y w lb hw hlb
    obtain ⟨w0', lb0, hw0', hlb0, he, hrel'⟩ := ctx_lbold S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w lb hw hlb
    have hl : lb.lastTriedBallot = lb0.lastTriedBallot := by
      rcases he with he | he <;> rw [he]
    rw [hl]
    rcases hrel' with rfl | ⟨-, -, hww, -, hle⟩
    · exact hA.lastLeBal r hr y w0' lb0 hw0' hlb0
    · rw [hww]; exact Int.le_trans (hA.lastLeBal r hr y w0' lb0 hw0' hlb0) hle
  · intro r hr; rw [(F r).2.1]; exact hA.peerOk r hr
  · intro r hr q hq
    exact Int.le_trans (by
      rw [(F r).2.2.2.2 q]
      split
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
        have := hA.crtMsg fr r _ x hpm (by rw [hx]; rfl)
        rw [← hpi] at *
        have h2 := hA.crtOwn r hr x.q hq
        omega
      · exact hA.crtOwn r hr q hq) (hcrt' q q)
  · intro r hr y w hw
    rcases hrel r y w hw with h | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Int.le_trans (hA.crtRec r hr y w h) (hcrt' _ _)
    · subst h2; exact Int.le_trans (hA.crtMsg fr i _ y hpm (by rw [hx]; rfl)) (hcrt' _ _)
    · subst h2; exact Int.le_trans (hA.crtMsg fr i _ y hpm (by rw [hx]; rfl)) (hcrt' _ _)
  · intro fr' to m y hm' hy
    exact Int.le_trans (hA.crtMsg fr' to m y ((hmsg _ _ _).mp hm') hy) (hcrt' _ _)
  · intro r e y he hy
    rcases ctx_ev S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r e he with h | ⟨-, rfl | rfl⟩
    · obtain ⟨c1, c2⟩ := hA.crtEv r e y h hy; exact ⟨c1, Int.le_trans c2 (hcrt' _ _)⟩
    · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
      exact ⟨hxq, Int.le_trans (hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)) (hcrt' _ _)⟩
    · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
      exact ⟨hxq, Int.le_trans (hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)) (hcrt' _ _)⟩
  · intro q hq j hj
    rw [hcq] at hj
    obtain ⟨w, lb, hw, hlb⟩ := hA.ownRow q hq j hj
    rcases R2 q _ w hw with ⟨h1, h2, h3⟩ | h
    · rw [h2, h1]; subst h3
      obtain ⟨lb', hlb', -⟩ := hlb2 lb hlb
      exact ⟨w', lb', R3, hlb'⟩
    · exact ⟨w, lb, h, hlb⟩
  · intro r hr y w lb hw hlb hs v hv
    obtain ⟨w0', lb0, hw0', hlb0, he, -⟩ := ctx_lbold S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w lb hw hlb
    have hl : lb.lastTriedBallot = lb0.lastTriedBallot ∧ lb.status = lb0.status := by
      rcases he with he | he <;> rw [he] <;> exact ⟨rfl, rfl⟩
    rw [hl.1] at hv; rw [hl.2] at hs
    exact hA.paNoAcc r hr y w0' lb0 hw0' hlb0 hs v (hold r _ hv (fun h => by cases h) (fun h => by cases h))
  · intro r hr y w lb hw hlb hs hp hc hb
    obtain ⟨w0', lb0, hw0', hlb0, he, hrel'⟩ := ctx_lbold S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w lb hw hlb
    have hl : lb.lastTriedBallot = lb0.lastTriedBallot ∧ lb.status = lb0.status := by
      rcases he with he | he <;> rw [he] <;> exact ⟨rfl, rfl⟩
    rw [hl.1] at hp hb ⊢; rw [hl.2] at hs
    rcases hrel' with rfl | ⟨-, -, hww, hcw, -⟩
    · obtain ⟨v, hv⟩ := hp
      exact hA.paLeader r hr y w0' lb0 hw0' hlb0 hs
        ⟨v, hold r _ hv (fun h => by cases h) (fun h => by cases h)⟩ hc hb
    · rw [hww] at hc; rw [comm_stGe hcw] at hc; cases hc
  · intro r hr y w lb hw hlb hp
    obtain ⟨w0', lb0, hw0', hlb0, he, -⟩ := ctx_lbold S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w lb hw hlb
    have hl : lb.lastTriedBallot = lb0.lastTriedBallot ∧ lb.preparing = lb0.preparing ∧
        lb.prepareReplies = lb0.prepareReplies ∧ lb.leaderResponded = lb0.leaderResponded := by
      rcases he with he | he <;> rw [he] <;> exact ⟨rfl, rfl, rfl, rfl⟩
    rw [hl.1, hl.2.2.1, hl.2.2.2]; rw [hl.2.1] at hp
    obtain ⟨c1, c2, c3, c4, c5⟩ := hA.prepNoProp r hr y w0' lb0 hw0' hlb0 hp
    exact ⟨c1, fun v hv => c2 v (hold r _ hv (fun h => by cases h) (fun h => by cases h)),
      fun v hv => c3 v (hold r _ hv (fun h => by cases h) (fun h => by cases h)), c4, c5⟩
  · intro fr' to y b; rw [hcnt0]; exact hA.paMsgOnce fr' to y b
  · intro fr' to y b; rw [hcnt0]; exact hA.accMsgOnce fr' to y b
  · intro r y b st v hst' hv
    rcases hA.paVoteDeliv r y b st v hst' (hvo _ _ _ _ _ hv) with ⟨v0, h1⟩ | h1
    · exact Or.inl ⟨v0, hH.ev_old h1⟩
    · exact Or.inr (fun fr' => hH.allDeliv_old (h1 fr') (fun _ m hm' => hnoP _ _ m hm'))
  · intro a r y b h1
    rw [hcnt0] at h1 ⊢
    obtain ⟨c1, c2⟩ := hA.parOnce a r y b h1
    exact ⟨c1, hH.allDeliv_old c2 (fun _ m hm' => hnoP _ _ m hm')⟩
  · intro a r m hm'
    obtain ⟨b', v, h1, h2⟩ := hA.arFrom a r m ((hmsg _ _ _).mp hm'); exact ⟨b', v, h1, hH.ev_old h2⟩
  · intro a r y b h1
    rw [hcnt0] at h1 ⊢
    rcases hA.arOnce a r y b h1 with h | ⟨h2, h3⟩
    · left
      obtain ⟨w, lb, hw, hlb, hlt⟩ := h
      rcases R2 r y w hw with ⟨e1, e2, e3⟩ | h
      · subst e1 e2 e3
        obtain ⟨lb', hlb', he'⟩ := hlb2 lb hlb
        refine ⟨w', lb', R3, hlb', ?_⟩
        rcases he' with he' | he' <;> rw [he'] <;> exact hlt
      · exact ⟨w, lb, h, hlb, hlt⟩
    · exact Or.inr ⟨h2, hH.allDeliv_old h3 (fun _ m hm' => hnoP _ _ m hm')⟩
  · intro fr' to m hm'; exact hA.commitBal fr' to m ((hmsg _ _ _).mp hm')
  · intro r to m he
    have he0 := hold r _ he (fun h => by cases h) (fun h => by cases h)
    obtain ⟨c1, c2, c3⟩ := hA.sentPR r to m he0
    have hnE : ∀ e', S.ev r e' → (e' ≠ .record x p.command) →
        (e' ≠ .commit x p.ballot ⟨p.command, p.seq, p.deps⟩) →
        S'.evBefore r (.sent to (.prepareReply m)) r e' →
        S.evBefore r (.sent to (.prepareReply m)) r e' := by
      intro e' h1 h2 h3 hb
      exact hH.evBefore_back hb h1 (fun _ => ctx_notE S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ h2 h3 rfl)
    refine ⟨fun hr => ?_, fun b st v hb => ?_, fun to' m2 hb hy => ?_⟩
    · obtain ⟨w, hw, hle⟩ := c1 hr
      rcases R2 r _ w hw with ⟨h1, h2, h3⟩ | h
      · subst h1 h3; rw [h2]; exact ⟨w', R3, Int.le_trans hle hwb⟩
      · exact ⟨w, h, hle⟩
    · have hv : S.ev r (.vote ⟨toN m.replica, toN m.inst⟩ b st v) := by
        obtain ⟨pp, pp', -, -, h⟩ := hb; exact hvo _ _ _ _ _ (List.mem_of_getElem? h)
      exact c2 b st v (hnE _ hv (fun h => by cases h) (fun h => by cases h) hb)
    · have hv : S.ev r (.sent to' (.acceptReply m2)) := by
        obtain ⟨pp, pp', -, -, h⟩ := hb
        exact hold r _ (List.mem_of_getElem? h) (fun h => by cases h) (fun h => by cases h)
      exact c3 to' m2 (hnE _ hv (fun h => by cases h) (fun h => by cases h) hb) hy
  · -- confCover
    have hcl : ∀ r, ConfProof.confLe (S.rep r) (S'.rep r) := by
      intro r
      by_cases hr : r = i
      · subst hr; rw [hH.rep_self]
        rcases hcase with ⟨-, -, hc⟩ | ⟨-, -, -, -, -, -, σb, hb, hc⟩
        · exact ConfProof.confLe_of_eq hc
        · exact ConfProof.confLe_trans (ConfProof.confLe_of_eq hb)
            (ConfProof.confLe_trans (ConfProof.uc_le σb p.command x.q p.inst p.seq)
              (ConfProof.confLe_of_eq hc))
      · rw [hH.rep_other hr]; exact ConfProof.confLe_refl _
    intro r hr e y cy he hrec c hc
    rcases (hH.ev_iff r e).mp he with h | ⟨hr', hE⟩
    · exact ConfProof.confLe_cover (hcl r) (hA.confCover r hr e y cy h hrec c hc)
    · subst hr'
      rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, -, -, -, rfl, σb, hb, hc'⟩
      · cases hE
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hE
        rcases hE with rfl | rfl
        · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
          obtain ⟨rfl, rfl⟩ := hrec
          rw [hH.rep_self, hc', hpi]
          exact ConfProof.uc_cov σb p.command _ p.inst p.seq c hc
        · simp [Event.recorded] at hrec
  · -- classWf
    have hgrow : ∀ y, (S.rep i).inst y ≠ none → σ'.inst y ≠ none := by
      intro y hy; rw [hσi]
      by_cases h : y = x
      · subst h; simp
      · rw [upd_other _ _ _ _ h]; exact hy
    have hxn : σ'.inst x ≠ none := by rw [hσi]; simp
    intro r hr
    by_cases hri : r = i
    · subst hri; rw [hH.rep_self]
      rcases hcls with ⟨h1, h2, -⟩ | ⟨σb, h1, h2, h3, h4, h5⟩
      · exact AuxProof.clsWf_keep (hA.classWf r hr) h1 h2 hgrow
      · have hb : AuxProof.ClsWf σb :=
          AuxProof.clsWf_keep (hA.classWf r hr) h1 h2 (fun y hy => by rw [h3]; exact hgrow y hy)
        have hu := ConfProof.clsWf_uc hb p.command x.q p.inst p.seq (fun h0 => by
          have : (⟨x.q, toN p.inst⟩ : InstId) = x := by
            rw [hx]
          rw [this, h3]; exact hxn)
        exact AuxProof.clsWf_keep hu h4 h5 (fun y hy => by
          rw [ConfProof.uc_inst, h3] at hy; exact hy)
    · rw [hH.rep_other hri]; exact hA.classWf r hr
  · -- classCover
    have hle : ∀ r, AuxProof.clsLe (S.rep r) (S'.rep r) := by
      intro r
      by_cases hr : r = i
      · subst hr; rw [hH.rep_self]
        rcases hcls with ⟨h1, h2, -⟩ | ⟨σb, h1, h2, -, h4, h5⟩
        · exact AuxProof.clsLe_of_eq h1 h2
        · exact AuxProof.clsLe_trans (AuxProof.clsLe_of_eq h1 h2)
            (AuxProof.clsLe_trans (ConfProof.uc_clsLe σb p.command x.q p.inst p.seq)
              (AuxProof.clsLe_of_eq h4 h5))
      · rw [hH.rep_other hr]; exact AuxProof.clsLe_refl _
    intro r hr e y cy he hrec
    rcases (hH.ev_iff r e).mp he with h | ⟨hr', hE⟩
    · exact AuxProof.clsCov_mono (hle r) (hA.classCover r hr e y cy h hrec)
    · subst hr'
      rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, -, -, -, rfl, -⟩
      · cases hE
      · rcases hcls with ⟨-, -, hE0⟩ | ⟨σb, -, -, -, h4, h5⟩
        · cases hE0
        · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hE
          rcases hE with rfl | rfl
          · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
            obtain ⟨rfl, rfl⟩ := hrec
            rw [hH.rep_self]; intro c hc'; rw [h4, h5]
            exact ConfProof.clsCov_uc σb p.command p.inst p.seq _ hpi.symm c hc'
          · simp [Event.recorded] at hrec
  · -- paAttrs
    intro r y b st v hst hv
    exact hH.ev_old (hA.paAttrs r y b st v hst (hvo _ _ _ _ _ hv))
  · -- valOk
    intro r y b v hv
    rw [hH.owner]
    exact hA.valOk r y b v (hv.imp (fun h => hold r _ h (fun h => by cases h) (fun h => by cases h))
      (fun h => hold r _ h (fun h => by cases h) (fun h => by cases h)))
  · -- cmdsNe
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
    refine ⟨fun fr' to m hm' cs hc => n1 fr' to m ((hmsg _ _ _).mp hm') cs hc,
      fun r hr y w cs hw hc => ?_, fun r hr y w lb cs hw hlb hc => ?_,
      fun fr' to m hm' hs => n4 fr' to m ((hmsg _ _ _).mp hm') hs,
      fun r m he => n5 r m (hold r _ he (fun h => by cases h) (fun h => by cases h)),
      fun r y b v hv => n6 r y b v (hv.imp (fun h => hold r _ h (fun h => by cases h) (fun h => by cases h))
        (fun h => hold r _ h (fun h => by cases h) (fun h => by cases h)))⟩
    · rcases hrel r y w hw with h | ⟨-, -, -, rfl⟩ | ⟨-, -, h3, -, -, -, -, hcm, -⟩
      · exact n2 r hr y w cs h hc
      · simp [newInstanceDefault] at hc
      · subst h3; rw [hcm] at hc; simp only [Option.some.injEq] at hc; subst hc
        exact n1 fr i _ hpm _ rfl
    · obtain ⟨w0', lb0, hw0', hlb0, hle, -⟩ := ctx_lbold S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y w lb hw hlb
      rcases hle with rfl | rfl
      · exact n3 r hr y w0' lb cs hw0' hlb0 hc
      · exact n3 r hr y w0' lb0 cs hw0' hlb0 hc
  · -- prSent
    intro fr' to m hm'
    exact hH.ev_old (hA.prSent fr' to m ((hmsg _ _ _).mp hm'))
  · -- selfOk
    intro r m he hs
    exact hA.selfOk r m (hold r _ he (fun h => by cases h) (fun h => by cases h)) hs
  · -- selfRaw
    intro r m he
    exact hA.selfRaw r m (hold r _ he (fun h => by cases h) (fun h => by cases h))
  · -- pm (sixth agent)
    exact ctx_pm S S' fr i n p x w0 w' σ' E hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  · -- ownerCrt (p-model2)
    intro y ps h; rw [hH.owner] at h
    obtain ⟨h1, h2⟩ := hA.ownerCrt y ps h
    exact ⟨h1, Int.le_trans h2 (hcrt' _ _)⟩
  · -- execLo (p-exec)
    exact AuxProof.execLo_upd hS.2.execLo hH.rep hexe

end

/-- **`handleCommit` keeps the invariant.** -/
theorem inv_deliver_commit' (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : Commit)
    (hm : (S.sent fr i)[n]? = some (.commit p))
    (hX : Inv0 (S.deliver fr i n (.commit p)) → InvExec (S.deliver fr i n (.commit p))) :
    Inv (S.deliver fr i n (.commit p)) := by
  obtain ⟨σ', E, hH, hid, hpo, hcrt, hexe, hsto, hcase⟩ := commit_cases_cls S fr i n p hidle hm
  have hcls : (σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut ∧ E = []) ∨
      ∃ σb : RState, σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
        σb.inst = σ'.inst ∧
        σ'.lastScan = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).lastScan ∧
        σ'.lastPut = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).lastPut := by
    rcases hcase with ⟨-, h2, -, h4, h5⟩ | ⟨-, -, -, -, -, -, σb, -, -, c3, c4, c5, c6, c7⟩
    · exact Or.inl ⟨h4, h5, h2⟩
    · exact Or.inr ⟨σb, c3, c4, c5, c6, c7⟩
  have hro := recOr_of (S.rep i) ⟨toN p.replica, toN p.inst⟩
  have hdn := deliver_delivered S fr i n (.commit p)
  generalize recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩ = w0 at hcase hro
  obtain ⟨w', hσi, hcase'⟩ : ∃ w', σ'.inst = upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ (some w') ∧
      ((w' = w0 ∧ E = [] ∧ σ'.conflicts = (S.rep i).conflicts) ∨
      (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧ lbo = some { lb with clientProposals := none }) ∧
        w' = comRec w0 lbo p ∧ ¬ isCommitted w0.status ∧ zz w0.bal ≤ zz p.ballot ∧
        E = [.record ⟨toN p.replica, toN p.inst⟩ p.command,
             .commit ⟨toN p.replica, toN p.inst⟩ p.ballot ⟨p.command, p.seq, p.deps⟩] ∧
        ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
          σ'.conflicts = (updateConflicts σb p.command (toN p.replica) p.inst p.seq).conflicts)) := by
    rcases hcase with ⟨h1, h2, h3, -, -⟩ | ⟨lbo, h1, h2, h3, h4, h5, σb, c1, c2, -⟩
    · exact ⟨w0, h1, Or.inl ⟨rfl, h2, h3⟩⟩
    · exact ⟨_, h2, Or.inr ⟨lbo, h1, rfl, not_comm_of h3, h4, h5, σb, c1, c2⟩⟩
  have hwf := ctx_wf S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn
  have hbal := ctx_ballots S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn
  obtain ⟨hmw, hrt, hnt, hown, hop, hvf, hcm, hpk⟩ := ctx_simple S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn
  have hsafe := ctx_safe S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn
  obtain ⟨hrr, hhi⟩ := ctx_rr S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn
  obtain ⟨hagr, hdc, hdcv, hwit, hac, hsl, hco⟩ := ctx_agr S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn
  obtain ⟨e1, e2, e3, e4⟩ := ctx_exec S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn
  have h0' : Inv0 (S.deliver fr i n (.commit p)) := ⟨hwf, hmw, hrt, hnt, hbal, hown, hop, hvf, hrr, hhi, ctx_lb S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn, hagr, hdc,
    chosenSafe_of_safe _ hwf hbal hown hvf hsafe, hdcv, hwit, hac, e1, e2, e3, e4, hsl, hco, hcm, hpk,
    hsafe, ctx_reports S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn⟩
  exact ⟨h0', ctx_aux S _ fr i n p _ w0 w' σ' E hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase' hdn (hX h0') hcls⟩

end CommitProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
