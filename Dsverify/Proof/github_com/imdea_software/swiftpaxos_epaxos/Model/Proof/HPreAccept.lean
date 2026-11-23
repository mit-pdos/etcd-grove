/-
`handlePreAccept` (`hPreAccept`): the law `inv_deliver_preAccept`.

Three cases (`preAccept_cases`): a stale PreAccept (`ballot < inst.bal`) changes nothing but the
record's creation and `crtInstance`; on a record at least ACCEPTED (with commands) only `bal`
moves up and the reply reports the record; otherwise the pre-accept vote with the attributes of
`updateAttributes` (`attrsRec`, recorded in the conflicts map) and its reply. (The branch "at
least ACCEPTED without commands" is unreachable: `InvAux.cmdsSome`.)
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HLocal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecHS
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Conf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HCommit

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PreAcceptProof

open HStepProof HLocal SafeProof ConfProof

/-- The record `hPreAccept` writes on a vote. -/
def paRec (w : InstRec) (p : PreAccept) (seq : w32) (deps : List w32) (st : w8) : InstRec :=
  { w with cmds := some p.command, seq := seq, deps := deps, bal := p.ballot, vbal := p.ballot,
           status := st }

/-- The reply on a vote / on a record at least ACCEPTED. -/
def paRep (p : PreAccept) (vb seq : w32) (deps cd : List w32) (st : w8) : PreAcceptReply :=
  { replica := p.replica, inst := p.inst, ballot := p.ballot, vballot := vb, seq := seq,
    deps := deps, committedDeps := cd, status := st }

/-- The cases of `hPreAccept` as a handler step. -/
theorem preAccept_cases (S : Sys) (fr i n : Nat) (p : PreAccept) (hidle : S.idle i)
    (hm : (S.sent fr i)[n]? = some (.preAccept p)) (hfr : fr < nR)
    (hldr : p.leaderId = W32 fr)
    (hcs : ∀ w, (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ = some w → w.status ≠ stNONE →
      w.cmds ≠ none) :
    let x : InstId := ⟨toN p.replica, toN p.inst⟩
    let w0 := recOr (S.rep i) x
    ∃ σ' w' E snd, HS S (S.deliver fr i n (.preAccept p)) i σ' E snd none ∧
      σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store ∧
      σ'.inst = upd (S.rep i).inst x (some w') ∧
      ((w' = w0 ∧ E = [] ∧ (∀ to, snd to = []) ∧ σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd, w' = { w0 with bal := p.ballot } ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = true ∧
         E = [.sent fr (.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status)] else []) ∧
         σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd seq deps st, ∃ σu : RState, σu.conflicts = (S.rep i).conflicts ∧
         deps = (updateAttributes σu p.command p.seq p.deps).2.1 ∧
         (st = stPREACCEPTED ∨ st = stPREACCEPTED_EQ) ∧
         w' = paRec w0 p seq deps st ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = false ∧
         E = [.vote x p.ballot st ⟨p.command, seq, deps⟩, .attrsRec x p.command deps,
              .sent fr (.preAcceptReply (paRep p p.ballot seq deps cd st))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p p.ballot seq deps cd st)] else []) ∧
         ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
           σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts ∧
           σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut ∧
           σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
           σb.inst = σ'.inst ∧
           σ'.lastScan = (updateConflicts σb p.command x.q p.inst p.seq).lastScan ∧
           σ'.lastPut = (updateConflicts σb p.command x.q p.inst p.seq).lastPut)) := by
  dsimp only
  have hH := hs_deliver S fr i n (.preAccept p) hidle hm
  simp only [hMsg] at hH
  have hl : toN p.leaderId = fr := by rw [hldr]; exact toN_W32 fr hfr
  have hro := recOr_of (S.rep i) ⟨toN p.replica, toN p.inst⟩
  unfold hPreAccept at hH
  generalize hσ1 : (if (S.rep i).maxSeq.sle p.seq = true then
    { S.rep i with maxSeq := p.seq + 1 } else S.rep i) = σ1 at hH
  have e1 : σ1.inst = (S.rep i).inst ∧ σ1.id = (S.rep i).id ∧
      σ1.peerOrder = (S.rep i).peerOrder ∧ σ1.crtInstance = (S.rep i).crtInstance ∧
      σ1.conflicts = (S.rep i).conflicts ∧ σ1.execedUpTo = (S.rep i).execedUpTo ∧
      σ1.store = (S.rep i).store := by
    rw [← hσ1]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hr : recOr (bumpCrt (bumpRecvBallot σ1 p.ballot) (toN p.replica) p.inst)
      ⟨toN p.replica, toN p.inst⟩ = recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩ := by
    simp [recOr, e1.1]
  simp only [getOrDefault_eq, hr] at hH
  generalize recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩ = w0 at hH hro ⊢
  generalize hσ2 : (bumpCrt (bumpRecvBallot σ1 p.ballot) (toN p.replica) p.inst).setInst
    ⟨toN p.replica, toN p.inst⟩ w0 = σ2 at hH
  have e2 : σ2.id = (S.rep i).id ∧ σ2.peerOrder = (S.rep i).peerOrder ∧
      σ2.crtInstance = (bumpCrt (S.rep i) (toN p.replica) p.inst).crtInstance ∧
      σ2.conflicts = (S.rep i).conflicts ∧ σ2.execedUpTo = (S.rep i).execedUpTo ∧
      σ2.store = (S.rep i).store := by
    rw [← hσ2]
    obtain ⟨-, a2, a3, a4, a5, a6, a7⟩ := e1
    refine ⟨by simp [RState.setInst, a2], by simp [RState.setInst, a3], ?_,
      by simp [RState.setInst, a5], by simp [RState.setInst, a6], by simp [RState.setInst, a7]⟩
    simp only [RState.setInst]
    funext q'; rw [bumpCrt_crt', bumpCrt_crt', bumpRB_crt, a4]
  have ecls : σ2.lastScan = (S.rep i).lastScan ∧ σ2.lastPut = (S.rep i).lastPut := by
    have h1 : σ1.lastScan = (S.rep i).lastScan ∧ σ1.lastPut = (S.rep i).lastPut := by
      rw [← hσ1]; split <;> exact ⟨rfl, rfl⟩
    rw [← hσ2]
    simp only [RState.setInst]
    rw [(AuxProof.bumpCrt_cls _ _ _).1, (AuxProof.bumpRB_cls _ _).1,
      (AuxProof.bumpCrt_cls _ _ _).2, (AuxProof.bumpRB_cls _ _).2]
    exact h1
  have hσ2i : ∀ w, (σ2.setInst ⟨toN p.replica, toN p.inst⟩ w).inst =
      upd (S.rep i).inst ⟨toN p.replica, toN p.inst⟩ (some w) := by
    intro w; rw [← hσ2]; simp [RState.setInst, e1.1]
  by_cases c1 : p.ballot.slt w0.bal = true
  · simp only [c1, if_true] at hH
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := e2
    refine ⟨σ2, w0, [], sendsOf [], by simpa [evsOf, pendFold] using hH, a1, a2, a3, a5, a6,
      ?_, Or.inl ⟨rfl, rfl, fun _ => rfl, a4, ecls.1, ecls.2⟩⟩
    rw [← hσ2]; simp [RState.setInst, e1.1]
  · have hle : zz w0.bal ≤ zz p.ballot := (slt_false _ _).mp (by simpa using c1)
    simp only [c1, if_false, Bool.false_eq_true] at hH
    by_cases c2 : stGe w0.status stACCEPTED = true
    · have hcm : w0.cmds ≠ none := by
        rcases hro with h | ⟨-, h⟩
        · refine hcs w0 h (fun h' => ?_)
          rw [h'] at c2; simp [stGe, stNONE, stACCEPTED] at c2
        · rw [h] at c2; simp [newInstanceDefault, stGe, stNONE, stACCEPTED] at c2
      simp only [c2, if_true, hcm, if_false] at hH
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := e2
      refine ⟨_, { w0 with bal := p.ballot }, _, _, hH, by simp [RState.setInst, a1],
        by simp [RState.setInst, a2], by simp [RState.setInst, a3], by simp [RState.setInst, a5],
        by simp [RState.setInst, a6], hσ2i _,
        Or.inr (Or.inl ⟨(σ2.setInst ⟨toN p.replica, toN p.inst⟩ { w0 with bal := p.ballot }).committedList,
          rfl, hle, c2, ?_, fun to => ?_, by simp [RState.setInst, a4], ecls.1, ecls.2⟩)⟩
      · simp [evsOf, Out.hev, hl, paRep]
      · simp only [sendsOf, List.nil_append, List.cons_append, List.filterMap_cons, List.filterMap_nil, Out.sendTo, hl]
        by_cases h : fr = to
        · subst h; simp [paRep]
        · simp [h, Ne.symm h]
    · simp only [c2, if_false, Bool.false_eq_true] at hH
      generalize hua : updateAttributes σ2 p.command p.seq p.deps = ua at hH
      obtain ⟨seq, deps, ch⟩ := ua
      simp only at hH
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := e2
      have hst : (if ch = true then stPREACCEPTED else stPREACCEPTED_EQ) = stPREACCEPTED ∨
          (if ch = true then stPREACCEPTED else stPREACCEPTED_EQ) = stPREACCEPTED_EQ := by
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
      generalize (if ch = true then stPREACCEPTED else stPREACCEPTED_EQ) = st at hH hst
      refine ⟨_, paRec w0 p seq deps st, _, _, hH, ?_, ?_, ?_, ?_, ?_, ?_,
        Or.inr (Or.inr ⟨(updateConflicts (σ2.setInst ⟨toN p.replica, toN p.inst⟩
            (paRec w0 p seq deps st)) p.command (toN p.replica) p.inst p.seq).committedList,
          seq, deps, st, σ2, a4, by rw [hua], hst, rfl, hle, by simpa using c2,
          ?_, fun to => ?_, _, by simp [RState.setInst, a4], rfl, ecls.1, ecls.2, ecls.1, ecls.2,
          (ConfProof.uc_inst _ _ _ _ _).symm, rfl, rfl⟩)⟩
      · simp [RState.setInst, (CommitProof.uc_fields _ _ _ _ _).2.1, a1]
      · simp [RState.setInst, (CommitProof.uc_fields _ _ _ _ _).2.2.1, a2]
      · simp [RState.setInst, (CommitProof.uc_fields _ _ _ _ _).2.2.2.1, a3]
      · simp [RState.setInst, (CommitProof.uc_fields _ _ _ _ _).2.2.2.2.1, a5]
      · simp [RState.setInst, (CommitProof.uc_fields _ _ _ _ _).2.2.2.2.2, a6]
      · rw [(CommitProof.uc_fields _ _ _ _ _).1, hσ2i]; rfl
      · simp [evsOf, Out.hev, hl, paRep, paRec]
      · simp only [sendsOf, List.nil_append, List.cons_append, List.filterMap_cons, List.filterMap_nil, Out.sendTo, hl]
        by_cases h : fr = to
        · subst h; simp [paRep, paRec]
        · simp [h, Ne.symm h]

/-! ## The step's context -/

/-- The vote case's data. -/
def VC (S : Sys) (i : Nat) (p : PreAccept) (w0 w' : InstRec) (seq : w32) (deps : List w32)
    (st : w8) : Prop :=
  (st = stPREACCEPTED ∨ st = stPREACCEPTED_EQ) ∧ w' = paRec w0 p seq deps st ∧
  zz w0.bal ≤ zz p.ballot ∧ stGe w0.status stACCEPTED = false ∧
  ∃ σu : RState, σu.conflicts = (S.rep i).conflicts ∧
    deps = (updateAttributes σu p.command p.seq p.deps).2.1 ∧
    σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut

/-- The reply's facts. -/
def RPok (S : Sys) (i fr : Nat) (p : PreAccept) (x : InstId) (w0 w' : InstRec) (E : List Event)
    (rp : PreAcceptReply) : Prop :=
  rp.replica = p.replica ∧ rp.inst = p.inst ∧ rp.ballot = p.ballot ∧
  ((rp.vballot = w0.vbal ∧ rp.seq = w0.seq ∧ rp.deps = w0.deps ∧ rp.status = w0.status ∧
     stGe w0.status stACCEPTED = true ∧ w' = { w0 with bal := p.ballot } ∧
     zz w0.bal ≤ zz p.ballot) ∨
   (∃ seq deps st, VC S i p w0 w' seq deps st ∧ rp.vballot = p.ballot ∧ rp.seq = seq ∧
     rp.deps = deps ∧ rp.status = st ∧
     EBefore E (.vote x p.ballot st ⟨p.command, seq, deps⟩) (.sent fr (.preAcceptReply rp))))

/-- The kinds of events the step makes. -/
def newKind (e : Event) : Prop :=
  (∃ to rp, e = .sent to (.preAcceptReply rp)) ∨ (∃ y b st v, e = .vote y b st v) ∨
  (∃ y c d, e = .attrsRec y c d)

theorem slotsOn_congr' (σ σ' : RState) (xs : List InstId) (k : w64)
    (h : ∀ y ∈ xs, (σ'.inst y).bind (·.cmds) = (σ.inst y).bind (·.cmds)) :
    Sys.slotsOn σ' xs k = Sys.slotsOn σ xs k := by
  simp only [Sys.slotsOn]
  exact flatMap_congr' (fun y hy => by rw [h y hy])

theorem isPA_not_ge {s : w8} (h : isPA s) : stGe s stACCEPTED = false := by
  rcases h with h | h <;> subst h <;> decide

theorem accComm_ge {s : w8} (h : s = stACCEPTED ∨ isCommitted s) : stGe s stACCEPTED = true := by
  rcases h with h | h | h <;> subst h <;> decide

section
variable (S S' : Sys) (fr i n : Nat) (p : PreAccept) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event) (snd : Nat → List Msg)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.preAccept p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E snd none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ (∀ to, snd to = []) ∧ σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd, w' = { w0 with bal := p.ballot } ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = true ∧
         E = [.sent fr (.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status)] else []) ∧
         σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd seq deps st, ∃ σu : RState, σu.conflicts = (S.rep i).conflicts ∧
         deps = (updateAttributes σu p.command p.seq p.deps).2.1 ∧
         (st = stPREACCEPTED ∨ st = stPREACCEPTED_EQ) ∧
         w' = paRec w0 p seq deps st ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = false ∧
         E = [.vote x p.ballot st ⟨p.command, seq, deps⟩, .attrsRec x p.command deps,
              .sent fr (.preAcceptReply (paRep p p.ballot seq deps cd st))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p p.ballot seq deps cd st)] else []) ∧
         ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
           σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts ∧
           σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut ∧
           σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
           σb.inst = σ'.inst ∧
           σ'.lastScan = (updateConflicts σb p.command x.q p.inst p.seq).lastScan ∧
           σ'.lastPut = (updateConflicts σb p.command x.q p.inst p.seq).lastPut))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

theorem ctx_basic :
    Msg.preAccept p ∈ S.msgs fr i ∧ p.leaderId = W32 fr ∧
    S.ev fr (.phase1 x p.ballot ⟨p.command, p.seq, p.deps⟩) ∧ S.ev fr (.makeBallot x p.ballot) ∧
    x.q < nR ∧ x.i + 1 < MAX_INSTANCE ∧ 0 ≤ zz p.inst ∧ (x.i : Int) = zz p.inst ∧
    0 ≤ zz p.ballot ∧ fr ≠ i ∧ depsOk p.deps ∧ p.command ≠ [] := by
  have hpm : Msg.preAccept p ∈ S.msgs fr i := mem_msgs_of_sent S hm
  obtain ⟨hldr, hph⟩ := hS.1.2.2.2.2.2.1.2.2.2.2.1 fr i p hpm
  rw [← hx] at hph
  have hmk : S.ev fr (.makeBallot x p.ballot) := by
    obtain ⟨q1, q2, -, h1, -⟩ := hS.1.2.2.2.2.2.1.2.1 fr x _ _ hph
    exact List.mem_of_getElem? h1
  obtain ⟨r1, r2, r3, r4⟩ := (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
  have hdeps := (hS.1.2.1 fr i _ hpm).2 p.deps (by simp [Msg.depsFields])
  refine ⟨hpm, hldr, hph, hmk, ?_, ?_, r3, ?_, zz_nonneg_of_make S hS.1.2.2.2.2.2.1 hmk,
    (hS.1.1.2.2.2.2.2.1 fr i (List.ne_nil_of_mem hpm)).2.2, hdeps, hS.preAccept_cmds_ne hpm⟩
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
      else zz ((S.rep r).crtInstance q)) ∧
    confLe (S.rep r) (S'.rep r) := by
  intro r
  rw [hH.rep]
  by_cases h : r = i
  · subst h; simp only [upd_same]
    refine ⟨hid, hpo, hexe, hsto, fun q => ?_, ?_⟩
    · rw [hcrt, zz_bumpCrt]
      by_cases hq : q = x.q
      · subst hq; simp
      · simp [hq]
    · rcases hcase with ⟨-, -, -, hc, -⟩ | ⟨-, -, -, -, -, -, hc, -⟩ |
        ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, σb, hb, hc, -⟩
      · exact confLe_of_eq hc
      · exact confLe_of_eq hc
      · exact confLe_trans (confLe_of_eq hb)
          (confLe_trans (uc_le σb p.command x.q p.inst p.seq) (confLe_of_eq hc))
  · simp only [upd_other _ _ _ _ h]
    refine ⟨by simp, by simp, by simp, by simp, fun q => by simp [h], confLe_refl _⟩

theorem ctx_crt_le : ∀ r q, zz ((S.rep r).crtInstance q) ≤ zz ((S'.rep r).crtInstance q) := by
  intro r q
  rw [(ctx_fields S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r).2.2.2.2.1 q]
  split <;> omega

theorem ctx_w0 : (w0.status = stNONE ∨ isPA w0.status ∨ w0.status = stACCEPTED ∨
      isCommitted w0.status) ∧ zz w0.vbal ≤ zz w0.bal ∧ w0.id = x := by
  rcases hro with h | ⟨-, rfl⟩
  · exact ⟨hS.2.stRange i hi x w0 h, hS.1.2.2.2.2.1.1 i hi x w0 h, (hS.1.1.2.1 i hi x w0 h).1⟩
  · exact ⟨Or.inl rfl, by simp [newInstanceDefault], rfl⟩

/-- The record at `(i, x)` after the step. -/
theorem ctx_X : ((S.rep i).inst x = some w0 ∧ w' = w0) ∨
    ((S.rep i).inst x = none ∧ w' = newInstanceDefault x ∧ w0 = newInstanceDefault x) ∨
    ((S.rep i).inst x = some w0 ∧ w' = { w0 with bal := p.ballot } ∧
      stGe w0.status stACCEPTED = true ∧ zz w0.bal ≤ zz p.ballot) ∨
    (∃ seq deps st, VC S i p w0 w' seq deps st ∧
      Event.vote x p.ballot st ⟨p.command, seq, deps⟩ ∈ E ∧ Event.attrsRec x p.command deps ∈ E) := by
  rcases hcase with ⟨he, -⟩ | ⟨cd, he, hle, hge, -⟩ | ⟨cd, seq, deps, st, σu, hu, hd, hst, he, hle, hge, hE, -, -, -, -, hus, hup, -⟩
  · rcases hro with h | ⟨h, h0⟩
    · exact Or.inl ⟨h, he⟩
    · exact Or.inr (Or.inl ⟨h, by rw [he, h0], h0⟩)
  · rcases hro with h | ⟨h, h0⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h, he, hge, hle⟩))
    · rw [h0] at hge; simp [newInstanceDefault, stGe, stNONE, stACCEPTED] at hge
  · exact Or.inr (Or.inr (Or.inr ⟨seq, deps, st, ⟨hst, he, hle, hge, σu, hu, hd, hus, hup⟩,
      by rw [hE]; simp, by rw [hE]; simp⟩))

theorem ctx_w : zz w0.bal ≤ zz w'.bal ∧ w'.lb = w0.lb ∧ w'.id = w0.id ∧ zz w'.vbal ≤ zz w'.bal ∧
    (w'.bal = w0.bal ∨ w'.bal = p.ballot) ∧
    (w'.status = w0.status ∨ isPA w'.status) ∧
    (isCommitted w0.status ∨ w0.status = stEXECUTED ∨ isCommitted w'.status ∨
      w'.status = stEXECUTED → w'.status = w0.status ∧ w'.cmds = w0.cmds ∧ w'.seq = w0.seq ∧
        w'.deps = w0.deps ∧ w'.vbal = w0.vbal) := by
  obtain ⟨hst0, hvb0, -⟩ := ctx_w0 S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  rcases hcase with ⟨rfl, -⟩ | ⟨cd, rfl, hle, hge, -⟩ | ⟨cd, seq, deps, st, σu, hu, hd, hst, rfl, hle, hge, -⟩
  · exact ⟨Int.le_refl _, rfl, rfl, hvb0, Or.inl rfl, Or.inl rfl, fun _ => by simp⟩
  · exact ⟨hle, rfl, rfl, Int.le_trans hvb0 hle, Or.inr rfl, Or.inl rfl,
      fun _ => by simp⟩
  · have hpa : isPA st := hst
    refine ⟨hle, rfl, rfl, Int.le_refl _, Or.inr rfl, Or.inr hpa, fun hc => ?_⟩
    exfalso
    simp only [paRec] at hc
    rcases hc with hc | hc | hc | hc
    · exact absurd (comm_stGeAcc hc) (by rw [hge]; decide)
    · rw [hc] at hge; exact absurd hge (by decide)
    · exact comm_not_pa hc hpa
    · rw [hc] at hpa; rcases hpa with h | h <;> exact absurd h (by decide)

theorem ctx_E : ∀ e ∈ E, (∃ rp, e = .sent fr (.preAcceptReply rp) ∧
      RPok S i fr p x w0 w' E rp) ∨
    (∃ seq deps st, VC S i p w0 w' seq deps st ∧
      (e = .vote x p.ballot st ⟨p.command, seq, deps⟩ ∨ e = .attrsRec x p.command deps)) := by
  intro e he
  rcases hcase with ⟨-, rfl, -⟩ | ⟨cd, h1, h2, h3, rfl, -⟩ | ⟨cd, seq, deps, st, σu, hu, hd, hst, h1, h2, h3, rfl, -, -, -, -, hus, hup, -⟩
  · cases he
  · simp only [List.mem_singleton] at he; subst he
    exact Or.inl ⟨_, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl, h3, h1, h2⟩⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    have hvc : VC S i p w0 w' seq deps st := ⟨hst, h1, h2, h3, σu, hu, hd, hus, hup⟩
    rcases he with rfl | rfl | rfl
    · exact Or.inr ⟨seq, deps, st, hvc, Or.inl rfl⟩
    · exact Or.inr ⟨seq, deps, st, hvc, Or.inr rfl⟩
    · exact Or.inl ⟨_, rfl, rfl, rfl, rfl, Or.inr ⟨seq, deps, st, hvc, rfl, rfl, rfl, rfl,
        0, 2, by omega, rfl, rfl⟩⟩

theorem ctx_snd : ∀ to m, m ∈ snd to → to = fr ∧ ∃ rp, m = .preAcceptReply rp ∧
    RPok S i fr p x w0 w' E rp ∧ Event.sent fr m ∈ E := by
  intro to m hm'
  rcases hcase with ⟨-, -, h, -⟩ | ⟨cd, h1, h2, h3, rfl, h, -⟩ | ⟨cd, seq, deps, st, σu, hu, hd, hst, h1, h2, h3, rfl, h, -, -, -, hus, hup, -⟩
  · rw [h] at hm'; cases hm'
  · rw [h] at hm'; split at hm'
    · rename_i ht; simp only [List.mem_singleton] at hm'; subst hm'
      exact ⟨ht, _, rfl, ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl, h3, h1, h2⟩⟩, by simp⟩
    · cases hm'
  · rw [h] at hm'; split at hm'
    · rename_i ht; simp only [List.mem_singleton] at hm'; subst hm'
      exact ⟨ht, _, rfl, ⟨rfl, rfl, rfl, Or.inr ⟨seq, deps, st, ⟨hst, h1, h2, h3, σu, hu, hd, hus, hup⟩,
        rfl, rfl, rfl, rfl, 0, 2, by omega, rfl, rfl⟩⟩, by simp⟩
    · cases hm'

theorem ctx_ev : ∀ r e, S'.ev r e → S.ev r e ∨ (r = i ∧ e ∈ E) := fun r e he => (hH.ev_iff r e).mp he

theorem ctx_E_kind : ∀ e ∈ E, newKind e := by
  intro e he
  rcases ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn e he with ⟨rp, rfl, -⟩ | ⟨seq, deps, st, -, rfl | rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)

/-- Events of other kinds are old. -/
theorem ctx_ev_old (r : Nat) (e : Event) (he : S'.ev r e) (hk : ¬ newKind e) : S.ev r e := by
  rcases (hH.ev_iff r e).mp he with h | ⟨-, h⟩
  · exact h
  · exact absurd (ctx_E_kind S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn e h) hk

theorem ctx_notE (e : Event) (hk : ¬ newKind e) : i = i → e ∉ E :=
  fun _ h => hk (ctx_E_kind S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn e h)

theorem ctx_msgs : ∀ fr' to m, m ∈ S'.msgs fr' to → m ∈ S.msgs fr' to ∨
    (fr' = i ∧ to = fr ∧ ∃ rp, m = .preAcceptReply rp ∧ RPok S i fr p x w0 w' E rp ∧
      Event.sent fr m ∈ E) := by
  intro fr' to m hm'
  rcases hH.mem_msgs.mp hm' with h | ⟨hf, h | h⟩
  · exact Or.inl h
  · subst fr'; exact Or.inr ⟨rfl, ctx_snd S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn to m h⟩
  · simp [intendedOf] at h

/-- In the vote case, `i` had no pre-accept or accept vote at the PreAccept's ballot. -/
theorem ctx_novb (seq : w32) (deps : List w32) (st : w8) (hvc : VC S i p w0 w' seq deps st) :
    ∀ st' v, (isPA st' ∨ st' = stACCEPTED) → ¬ S.ev i (.vote x p.ballot st' v) := by
  obtain ⟨hpm, -, hph, hmk, hxq, -, -, -, -, hfi, -, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, -, hle, hge, -⟩ := hvc
  intro st' v hst' hv
  obtain ⟨w, hw, hb⟩ := hS.1.2.2.2.2.1.2 i hi x _ _ _ hv
  have hw0 : (S.rep i).inst x = some w0 := by
    rcases hro with h | ⟨h, -⟩
    · exact h
    · rw [h] at hw; cases hw
  rw [hw0] at hw; cases hw
  rcases hst' with hpa | hacc
  · rcases hS.2.paVoteDeliv i x p.ballot st' v hpa hv with ⟨v0, h0⟩ | h0
    · exact hfi (hS.1.2.2.2.2.2.2.1.1 fr i x p.ballot _ v0 hph h0).1
    · exact hn (h0 fr n _ (msgs_of_sent S hm) (by simp [Msg.isPAat, hx]))
  · subst hacc
    have := hS.2.accKeep i hi x w0 hw0 _ v hv (by
      have := hS.1.2.2.2.2.1.1 i hi x w0 hw0; omega)
    rw [accComm_ge this] at hge; cases hge

end

section
variable (S S' : Sys) (fr i n : Nat) (p : PreAccept) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event) (snd : Nat → List Msg)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.preAccept p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E snd none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ (∀ to, snd to = []) ∧ σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd, w' = { w0 with bal := p.ballot } ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = true ∧
         E = [.sent fr (.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status)] else []) ∧
         σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd seq deps st, ∃ σu : RState, σu.conflicts = (S.rep i).conflicts ∧
         deps = (updateAttributes σu p.command p.seq p.deps).2.1 ∧
         (st = stPREACCEPTED ∨ st = stPREACCEPTED_EQ) ∧
         w' = paRec w0 p seq deps st ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = false ∧
         E = [.vote x p.ballot st ⟨p.command, seq, deps⟩, .attrsRec x p.command deps,
              .sent fr (.preAcceptReply (paRep p p.ballot seq deps cd st))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p p.ballot seq deps cd st)] else []) ∧
         ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
           σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts ∧
           σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut ∧
           σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
           σb.inst = σ'.inst ∧
           σ'.lastScan = (updateConflicts σb p.command x.q p.inst p.seq).lastScan ∧
           σ'.lastPut = (updateConflicts σb p.command x.q p.inst p.seq).lastPut))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

/-- A committed or executed record (before or after) keeps what the executor and agreement read. -/
theorem ctx_view : ∀ r y, ((∃ w, (S.rep r).inst y = some w ∧
      (isCommitted w.status ∨ w.status = stEXECUTED)) ∨
    (∃ w, (S'.rep r).inst y = some w ∧ (isCommitted w.status ∨ w.status = stEXECUTED))) →
    ∃ w w2, (S.rep r).inst y = some w ∧ (S'.rep r).inst y = some w2 ∧ w2.status = w.status ∧
      w2.cmds = w.cmds ∧ w2.seq = w.seq ∧ w2.deps = w.deps ∧ w2.vbal = w.vbal ∧ w2.lb = w.lb ∧
      zz w.bal ≤ zz w2.bal := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, hlb, -, -, -, -, hcw⟩ := ctx_w S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro r y h
  by_cases hc : r = i ∧ y = x
  · obtain ⟨rfl, rfl⟩ := hc
    have hw0 : (S.rep r).inst y = some w0 ∧ (isCommitted w0.status ∨ w0.status = stEXECUTED ∨
        isCommitted w'.status ∨ w'.status = stEXECUTED) := by
      rcases h with ⟨w, hw, hs⟩ | ⟨w, hw, hs⟩
      · rcases hro with h' | ⟨h', -⟩
        · rw [h'] at hw; cases hw; exact ⟨h', hs.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
        · rw [h'] at hw; cases hw
      · rw [R3] at hw; cases hw
        have hs' : isCommitted w0.status ∨ w0.status = stEXECUTED ∨ isCommitted w'.status ∨
            w'.status = stEXECUTED := Or.inr (Or.inr hs)
        have := (hcw hs').1
        rcases hro with h' | ⟨-, h0⟩
        · exact ⟨h', hs'⟩
        · exfalso; rw [this, h0] at hs
          rcases hs with hs | hs
          · exact none_not_comm hs
          · simp [newInstanceDefault, stNONE, stEXECUTED] at hs
    obtain ⟨e1, e2, e3, e4, e5⟩ := hcw hw0.2
    exact ⟨w0, w', hw0.1, R3, e1, e2, e3, e4, e5, hlb, hwb⟩
  · have he := R4 r y (by
      by_cases h1 : r = i
      · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
      · exact Or.inl h1)
    rcases h with ⟨w, hw, -⟩ | ⟨w, hw, -⟩
    · exact ⟨w, w, hw, by rw [he]; exact hw, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩
    · rw [he] at hw
      exact ⟨w, w, hw, by rw [he]; exact hw, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩

theorem ctx_executed : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
  intro r y
  constructor
  · rintro ⟨w, hw, hs⟩
    obtain ⟨w1, w2, h1, h2, e1, -⟩ := ctx_view S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y (Or.inr ⟨w, hw, Or.inr hs⟩)
    rw [hw] at h2; cases h2
    exact ⟨w1, h1, by rw [← e1]; exact hs⟩
  · rintro ⟨w, hw, hs⟩
    obtain ⟨w1, w2, h1, h2, e1, -⟩ := ctx_view S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y (Or.inl ⟨w, hw, Or.inr hs⟩)
    rw [hw] at h1; cases h1
    exact ⟨w2, h2, by rw [e1]; exact hs⟩

theorem ctx_grow : ∀ r y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro r y h h'
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp h
  rcases R2 r y w hw with ⟨rfl, rfl, -⟩ | h2
  · rw [R3] at h'; cases h'
  · rw [h2] at h'; cases h'

/-- The vote case's deps are followable. -/
theorem ctx_depsOk (seq : w32) (deps : List w32) (st : w8) (hvc : VC S i p w0 w' seq deps st) :
    depsOk deps := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdeps, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, -, -, -, σu, hu, rfl, hus, hup⟩ := hvc
  obtain ⟨u1, u2, -, u4⟩ := ua_spec σu p.command p.seq p.deps
  have hl : p.deps.length = nR := hdeps.1
  refine ⟨by rw [u1, hl], fun d hd => ?_⟩
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hd
  have hq' : q < p.deps.length := by rw [← u1]; exact hq
  have hqn : q < nR := by rw [← hl]; exact hq'
  have hget : (updateAttributes σu p.command p.seq p.deps).2.1[q] =
      (updateAttributes σu p.command p.seq p.deps).2.1.getD q (W32 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  have hget0 : p.deps.getD q (W32 0) = p.deps[q] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq']
  rw [hget]
  rcases u4 q with h | ⟨hsrc, hlt⟩
  · rw [h, hget0]; exact hdeps.2 _ (List.getElem_mem hq')
  · have hm1 : -1 ≤ zz (p.deps.getD q (W32 0)) := by
      rw [hget0]
      rcases hdeps.2 _ (List.getElem_mem hq') with h | ⟨h, -⟩
      · simp only [zz]; omega
      · simp only [zz]; omega
    have h0 : 0 ≤ zz ((updateAttributes σu p.command p.seq p.deps).2.1.getD q (W32 0)) := by omega
    refine Or.inr ⟨h0, ?_⟩
    have hne : (S.rep i).inst ⟨q, toN ((updateAttributes σu p.command p.seq p.deps).2.1.getD q (W32 0))⟩ ≠ none := by
      generalize (updateAttributes σu p.command p.seq p.deps).2.1.getD q (W32 0) = d at h0 hsrc ⊢
      rcases hsrc with ⟨k, pp, hk, hpk⟩ | h | h | h
      · rw [hu] at hk
        obtain ⟨k1, k2, k3⟩ := hS.1.1.2.2.2.1 i hi q k pp hk
        rcases hpk with h | h <;> subst h
        · exact k2 h0
        · exact k3 h0
      · subst h; rw [hus] at h0 ⊢; exact (hS.2.classWf i hi q hqn).1 h0
      · subst h; rw [hup] at h0 ⊢; exact (hS.2.classWf i hi q hqn).2.1 h0
      · subst h; exact absurd h0 (by decide)
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
    exact (hS.1.1.2.1 i hi _ w hw).2.2.1

theorem ctx_wf : Inv.wf S' := by
  obtain ⟨hpm, hldr, hph, hmk, hxq, hxi, hpi0, hpi, hb0, hfi, hdeps, hcne⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have F := ctx_fields S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hS.1.1
  have hA := hS.2
  obtain ⟨hwb, hlb, hid', -, -, -, hcw⟩ := ctx_w S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hX := ctx_X S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hgrow := ctx_grow S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hw0 : w0.id = x ∧
      (∀ lb, w0.lb = some lb → lb.status ≠ stNONE → depsOk lb.deps) ∧
      (x.q = i → w0.lb ≠ none) ∧
      (∀ lb ps, w0.lb = some lb → lb.clientProposals = some ps → S.owner x = some ps) := by
    rcases hro with h | ⟨h, rfl⟩
    · obtain ⟨g1, -, -, -, g5, g6, g7⟩ := w2 i hi x w0 h
      exact ⟨g1, g5, g6, g7⟩
    · refine ⟨rfl, fun lb h' => by simp [newInstanceDefault] at h', fun hq => ?_,
        fun lb ps h' => by simp [newInstanceDefault] at h'⟩
      exfalso
      have hc := hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)
      rw [← hq] at h
      obtain ⟨w, lb, hw, -⟩ := hA.ownRow x.q hxq x.i hc
      rw [show (⟨x.q, x.i⟩ : InstId) = x from rfl, h] at hw; cases hw
  have hdw : w'.status ≠ stNONE → depsOk w'.deps := by
    intro hs
    rcases hX with ⟨h, rfl⟩ | ⟨-, rfl, -⟩ | ⟨h, rfl, hge, -⟩ | ⟨seq, deps, st, hvc, -⟩
    · exact (w2 i hi x _ h).2.2.2.1 hs
    · exact absurd rfl hs
    · exact (w2 i hi x w0 h).2.2.2.1 hs
    · rw [hvc.2.1]; exact ctx_depsOk S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn seq deps st hvc
  refine ⟨fun r hr => by rw [(F r).1]; exact w1 r hr, fun r hr y w hw => ?_,
    fun r hr q hq => ?_, fun r hr q k p0 hk => ?_, fun r hr q hq m' hm' => ?_,
    fun fr' to hne => ?_, fun fr' to n' hn' => ?_, fun r b hb => ?_⟩
  · rcases R1 r y w hw with ⟨rfl, rfl, rfl⟩ | h
    · obtain ⟨g1, g3, g4, g5⟩ := hw0
      refine ⟨hid' ▸ g1, hxq, hxi, hdw, fun lb hlb' => g3 lb (hlb ▸ hlb'), fun hq => hlb ▸ g4 hq,
        fun lb ps hlb' => ?_⟩
      rw [hH.owner]; exact g5 lb ps (hlb ▸ hlb')
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2 r hr y w h
      exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
  · have e := (F r).2.2.2.2.1 q
    obtain ⟨c1, c2⟩ := w3 r hr q hq
    simp only [toN, zz] at e c1 c2 hxi hpi hpi0 ⊢
    rw [e]
    split
    · constructor <;> omega
    · exact ⟨c1, c2⟩
  · by_cases hri : r = i
    · subst hri
      have hS'i := hH.rep_self
      rw [hS'i] at hk
      have G : ∀ (σb : RState), σb.conflicts = (S.rep r).conflicts →
          ∀ q k p0, σb.conflicts q k = some p0 →
            (fun q d => q < nR ∧ (0 ≤ zz d → (S'.rep r).inst ⟨q, toN d⟩ ≠ none)) q p0.last ∧
            (fun q d => q < nR ∧ (0 ≤ zz d → (S'.rep r).inst ⟨q, toN d⟩ ≠ none)) q p0.lastWrite := by
        intro σb hb q k p0 hk
        rw [hb] at hk
        obtain ⟨k1, k2, k3⟩ := w4 r hr q k p0 hk
        exact ⟨⟨k1, fun h => hgrow _ _ (k2 h)⟩, ⟨k1, fun h => hgrow _ _ (k3 h)⟩⟩
      have hcf : σ'.conflicts = (S.rep r).conflicts ∨ ∃ σb : RState, σb.conflicts = (S.rep r).conflicts ∧
          σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts := by
        rcases hcase with ⟨-, -, -, hc, -⟩ | ⟨-, -, -, -, -, -, hc, -⟩ |
          ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, σb, hb, hc, -⟩
        · exact Or.inl hc
        · exact Or.inl hc
        · exact Or.inr ⟨σb, hb, hc⟩
      rcases hcf with hc | ⟨σb, hb, hc⟩
      · rw [hc] at hk
        obtain ⟨⟨a1, a2⟩, ⟨-, a3⟩⟩ := G (S.rep r) rfl q k p0 hk
        exact ⟨a1, a2, a3⟩
      · rw [hc] at hk
        obtain ⟨⟨a1, a2⟩, ⟨-, a3⟩⟩ := CommitProof.uc_conf σb p.command x.q p.inst p.seq
          (fun q d => q < nR ∧ (0 ≤ zz d → (S'.rep r).inst ⟨q, toN d⟩ ≠ none))
          (G σb hb) ⟨hxq, fun _ => by
            rw [show (⟨x.q, toN p.inst⟩ : InstId) = x by rw [hx]]; rw [R3]; simp⟩
          ⟨hxq, fun h => absurd h (by decide)⟩ q k p0 hk
        exact ⟨a1, a2, a3⟩
    · rw [hH.rep_other hri] at hk ⊢
      exact w4 r hr q k p0 hk
  · rw [(F r).2.2.1] at hm'
    exact (ctx_executed S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _).mpr (w5 r hr q hq m' hm')
  · rw [hH.msgs] at hne
    by_cases h0 : S.msgs fr' to = []
    · rw [h0, List.nil_append] at hne
      split at hne
      · rename_i hf; rw [hf]
        simp only [intendedOf, List.append_nil] at hne
        obtain ⟨m', hm''⟩ := List.exists_mem_of_ne_nil _ hne
        obtain ⟨rfl, -⟩ := ctx_snd S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn to m' hm''
        exact ⟨hi, hfr, Ne.symm hfi⟩
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
variable (S S' : Sys) (fr i n : Nat) (p : PreAccept) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event) (snd : Nat → List Msg)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.preAccept p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E snd none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ (∀ to, snd to = []) ∧ σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd, w' = { w0 with bal := p.ballot } ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = true ∧
         E = [.sent fr (.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status)] else []) ∧
         σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd seq deps st, ∃ σu : RState, σu.conflicts = (S.rep i).conflicts ∧
         deps = (updateAttributes σu p.command p.seq p.deps).2.1 ∧
         (st = stPREACCEPTED ∨ st = stPREACCEPTED_EQ) ∧
         w' = paRec w0 p seq deps st ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = false ∧
         E = [.vote x p.ballot st ⟨p.command, seq, deps⟩, .attrsRec x p.command deps,
              .sent fr (.preAcceptReply (paRep p p.ballot seq deps cd st))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p p.ballot seq deps cd st)] else []) ∧
         ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
           σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts ∧
           σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut ∧
           σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
           σb.inst = σ'.inst ∧
           σ'.lastScan = (updateConflicts σb p.command x.q p.inst p.seq).lastScan ∧
           σ'.lastPut = (updateConflicts σb p.command x.q p.inst p.seq).lastPut))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

/-- The new votes. -/
theorem ctx_vote : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v) ∨
    (r = i ∧ y = x ∧ b = p.ballot ∧ ∃ seq deps, VC S i p w0 w' seq deps st ∧
      v = ⟨p.command, seq, deps⟩ ∧ Event.vote x p.ballot st ⟨p.command, seq, deps⟩ ∈ E) := by
  intro r y b st v he
  rcases (hH.ev_iff r _).mp he with h | ⟨hr, h⟩
  · exact Or.inl h
  · rcases ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ h with ⟨rp, h1, -⟩ | ⟨seq, deps, st', hvc, h1 | h1⟩
    · cases h1
    · simp only [Event.vote.injEq] at h1; obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact Or.inr ⟨hr, rfl, rfl, seq, deps, hvc, rfl, h⟩
    · cases h1

theorem ctx_rpok (rp : PreAcceptReply) (h : RPok S i fr p x w0 w' E rp) :
    (⟨toN rp.replica, toN rp.inst⟩ : InstId) = x ∧ rp.ballot = p.ballot ∧
    ((rp.vballot = w0.vbal ∧ rp.seq = w0.seq ∧ rp.deps = w0.deps ∧ rp.status = w0.status ∧
      stGe w0.status stACCEPTED = true ∧ w' = { w0 with bal := p.ballot } ∧
      (S.rep i).inst x = some w0) ∨
     (∃ seq deps st, VC S i p w0 w' seq deps st ∧ rp.vballot = p.ballot ∧ rp.seq = seq ∧
       rp.deps = deps ∧ rp.status = st ∧ Event.vote x p.ballot st ⟨p.command, seq, deps⟩ ∈ E ∧
       EBefore E (.vote x p.ballot st ⟨p.command, seq, deps⟩) (.sent fr (.preAcceptReply rp)))) := by
  obtain ⟨h1, h2, h3, h4 | ⟨seq, deps, st, hvc, e1, e2, e3, e4, hEB⟩⟩ := h
  · refine ⟨by rw [h1, h2, hx], h3, Or.inl ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1,
      h4.2.2.2.2.2.1, ?_⟩⟩
    rcases hro with h | ⟨-, h0⟩
    · exact h
    · have := h4.2.2.2.2.1; rw [h0] at this
      simp [newInstanceDefault, stGe, stNONE, stACCEPTED] at this
  · refine ⟨by rw [h1, h2, hx], h3, Or.inr ⟨seq, deps, st, hvc, e1, e2, e3, e4, ?_, hEB⟩⟩
    obtain ⟨q1, q2, -, h5, -⟩ := hEB; exact List.mem_of_getElem? h5

theorem ctx_msgWf : Inv.msgWf S' := by
  obtain ⟨hpm, -, -, -, -, -, -, -, -, -, -, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to m hm' with h | ⟨-, -, rp, rfl, hrp, -⟩
  · exact hS.1.2.1 fr' to m h
  · obtain ⟨h1, h2, -, -⟩ := id hrp
    refine ⟨fun q n' h => ?_, fun ds hds => ?_⟩
    · simp only [Msg.rawId, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [h1, h2]; exact (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
    · simp only [Msg.depsFields, List.mem_singleton] at hds; subst hds
      obtain ⟨-, -, h | ⟨seq, deps, st, hvc, -, -, e3, -⟩⟩ := ctx_rpok S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn rp hrp
      · obtain ⟨-, -, e3, -, e5, -, hw0⟩ := h
        rw [e3]
        refine (hS.1.1.2.1 i hi x w0 hw0).2.2.2.1 (fun h0 => ?_)
        rw [h0] at e5; simp [stGe, stNONE, stACCEPTED] at e5
      · rw [e3]; exact ctx_depsOk S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn seq deps st hvc

theorem ctx_rt : Inv.replyTargets S' := by
  obtain ⟨-, -, -, hmk, -, -, -, -, -, hfi, -, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, hlbeq, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro fr' to m y hm' hy hk
  rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to m hm' with h | ⟨-, hto, rp, rfl, hrp, -⟩
  · obtain ⟨w, lb, hw, hlb⟩ := hS.1.2.2.1 fr' to m y h hy hk
    rcases R2 to y w hw with ⟨h1, h2, h3⟩ | h'
    · subst to y w; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb⟩
    · exact ⟨w, lb, h', hlb⟩
  · simp only [Msg.instOf, Option.some.injEq] at hy
    obtain ⟨hx', -⟩ := ctx_rpok S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn rp hrp
    obtain ⟨w, lb, hw, hlb, -⟩ := hS.2.makerLb fr x p.ballot hfr hmk
    refine ⟨w, lb, ?_, hlb⟩
    rw [hto, R4 _ _ (Or.inl hfi), ← hy, hx']; exact hw

theorem ctx_ntpa : Inv.noTPA S' := by
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to m hm' with h | ⟨-, -, rp, rfl, -⟩
  · exact hS.1.2.2.2.1 fr' to m h
  · exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem ctx_ballots : Inv.ballots S' := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, -, -, hvb, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r hr y w hw => ?_, fun r hr y b st v he => ?_⟩
  · rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w; exact hvb
    · exact hS.1.2.2.2.2.1.1 r hr y w h
  · rcases ctx_vote S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b st v he with h | ⟨rfl, rfl, rfl, seq, deps, hvc, -⟩
    · obtain ⟨w, hw, hle⟩ := hS.1.2.2.2.2.1.2 r hr y b st v h
      rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h'
      · subst r y w; exact ⟨w', R3, Int.le_trans hle hwb⟩
      · exact ⟨w, h', hle⟩
    · refine ⟨w', R3, ?_⟩; rw [hvc.2.1]; simp [paRec]

theorem ctx_own : Inv.ballotOwner S' := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hS.1.2.2.2.2.2.1
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hnot := ctx_notE S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r y b he => ?_, fun r y b v he => ?_, fun r y b v he => ?_, fun r to m hm' => ?_,
    fun r to m hm' => ?_, fun r to m hm' => ?_⟩
  · have h := hold r _ he (by simp [newKind])
    refine ⟨(o1 r y b h).1, ?_⟩
    by_cases hr : r = i
    · rw [hH.count_eq (fun _ => hnot _ (by simp [newKind]) rfl)]; exact (o1 r y b h).2
    · rw [hH.count_eq (fun h => absurd h hr)]; exact (o1 r y b h).2
  · exact hH.evBefore_old (o2 r y b v (hold r _ he (by simp [newKind])))
  · exact hH.ev_old (o3 r y b v (hold r _ he (by simp [newKind])))
  · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r to _ hm' with h | ⟨-, -, rp, h, -⟩
    · obtain ⟨c1, c2⟩ := o4 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h
  · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r to _ hm' with h | ⟨-, -, rp, h, -⟩
    · obtain ⟨c1, c2⟩ := o5 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h
  · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r to _ hm' with h | ⟨-, -, rp, h, -⟩
    · obtain ⟨c1, c2⟩ := o6 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h

theorem ctx_op : Inv.oneProposal S' := by
  obtain ⟨p1, p2, p3⟩ := hS.1.2.2.2.2.2.2.1
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hnot := ctx_notE S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r r' y b v v' he he' => ?_, fun r r' y b v v' he he' => ?_,
    fun r r' y b v v' he he' => ?_⟩
  · have h := hold r _ he (by simp [newKind])
    have h' := hold r' _ he' (by simp [newKind])
    obtain ⟨c1, c2, c3⟩ := p1 r r' y b v v' h h'
    refine ⟨c1, c2, ?_⟩
    by_cases hr : r = i
    · rw [hH.count_eq (fun _ => hnot _ (by simp [newKind]) rfl)]; exact c3
    · rw [hH.count_eq (fun h => absurd h hr)]; exact c3
  · exact p2 r r' y b v v' (hold r _ he (by simp [newKind])) (hold r' _ he' (by simp [newKind]))
  · exact p3 r r' y b v v' (hold r _ he (by simp [newKind])) (hold r' _ he' (by simp [newKind]))

theorem ctx_vf : Inv.votesFollowProposals S' := by
  obtain ⟨-, -, hph, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨v1, v2⟩ := hS.1.2.2.2.2.2.2.2.1
  refine ⟨fun r y b st v he hst => ?_, fun r y b v he => ?_⟩
  · rcases ctx_vote S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b st v he with h | ⟨-, rfl, rfl, seq, deps, -, rfl, -⟩
    · obtain ⟨l, v0, h1, h2⟩ := v1 r y b st v h hst; exact ⟨l, v0, hH.ev_old h1, h2⟩
    · exact ⟨fr, _, hH.ev_old hph, rfl⟩
  · rcases ctx_vote S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b _ v he with h | ⟨-, -, -, seq, deps, hvc, -⟩
    · obtain ⟨l, h1⟩ := v2 r y b v h; exact ⟨l, hH.ev_old h1⟩
    · exfalso; rcases hvc.1 with h | h <;> exact absurd h (by decide)

theorem ctx_cv : ∀ y v, S'.committedVal y v ↔ S.committedVal y v := by
  intro y v
  constructor
  · rintro (⟨r, b, h⟩ | ⟨fr', to, m, hm', hy, rfl⟩)
    · exact Or.inl ⟨r, b, ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ h (by simp [newKind])⟩
    · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to _ hm' with h | ⟨-, -, rp, h, -⟩
      · exact Or.inr ⟨fr', to, m, h, hy, rfl⟩
      · cases h
  · rintro (⟨r, b, h⟩ | ⟨fr', to, m, hm', hy, rfl⟩)
    · exact Or.inl ⟨r, b, hH.ev_old h⟩
    · exact Or.inr ⟨fr', to, m, hH.msgs_old hm', hy, rfl⟩

theorem ctx_prep : ∀ r m e, S'.prepReport r m e → S.prepReport r m e ∧ (r = i → e ∉ E) := by
  rintro r m e ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
  · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r to _ hm' with h | ⟨-, -, rp, h, -⟩
    · exact ⟨⟨ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he (by simp [newKind]), Or.inl ⟨to, h, rfl⟩⟩,
        fun _ => ctx_notE S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (by simp [newKind]) rfl⟩
    · cases h
  · exact ⟨⟨ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he (by simp [newKind]), Or.inr rfl⟩,
      fun _ => ctx_notE S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (by simp [newKind]) rfl⟩

theorem ctx_repBal : ∀ m e, S.prepReport i m e → (⟨toN m.replica, toN m.inst⟩ : InstId) = x →
    zz m.ballot ≤ zz w0.bal := by
  intro m e hp hy
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrepo⟩ :=
    hS.1
  obtain ⟨w, hw, hle⟩ := hrepo.2.2.2.2.1 i m e hi hp
  have : (S.rep i).inst x = some w := by rw [← hy]; exact hw
  rcases hro with h | ⟨h, -⟩
  · rw [h] at this; cases this; exact hle
  · rw [h] at this; cases this

end

section
variable (S S' : Sys) (fr i n : Nat) (p : PreAccept) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event) (snd : Nat → List Msg)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.preAccept p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E snd none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ (∀ to, snd to = []) ∧ σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd, w' = { w0 with bal := p.ballot } ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = true ∧
         E = [.sent fr (.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status)] else []) ∧
         σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd seq deps st, ∃ σu : RState, σu.conflicts = (S.rep i).conflicts ∧
         deps = (updateAttributes σu p.command p.seq p.deps).2.1 ∧
         (st = stPREACCEPTED ∨ st = stPREACCEPTED_EQ) ∧
         w' = paRec w0 p seq deps st ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = false ∧
         E = [.vote x p.ballot st ⟨p.command, seq, deps⟩, .attrsRec x p.command deps,
              .sent fr (.preAcceptReply (paRep p p.ballot seq deps cd st))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p p.ballot seq deps cd st)] else []) ∧
         ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
           σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts ∧
           σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut ∧
           σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
           σb.inst = σ'.inst ∧
           σ'.lastScan = (updateConflicts σb p.command x.q p.inst p.seq).lastScan ∧
           σ'.lastPut = (updateConflicts σb p.command x.q p.inst p.seq).lastPut))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

theorem ctx_rr : Inv.repliesReportVotes S' := by
  obtain ⟨q1, q2, q3⟩ := hS.1.2.2.2.2.2.2.2.2.1
  obtain ⟨hpm, -, hph, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r m e hp => ?_, fun a r m hm' => ?_, fun a r m hm' => ?_⟩
  · obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r m e hp
    obtain ⟨c1, c2, c3, c4, c5⟩ := q1 r m e hp0
    refine ⟨c1, fun hs => hH.evBefore_old (c2 hs), fun hs => (hcv _ _).mpr (c3 hs),
      fun hs b st v hb => c4 hs b st v (hH.evBefore_back hb hp0.1 hne), fun b st v hb => ?_⟩
    rcases (hH.evBefore_iff _ _ _ _).mp hb with h | ⟨-, hr, h⟩ | ⟨hr, -, pp, pp', -, h, -⟩
    · exact c5 b st v h
    · subst r
      rcases ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ h with ⟨rp, h1, -⟩ | ⟨seq, deps, st', hvc, h1 | h1⟩
      · cases h1
      · simp only [Event.vote.injEq] at h1; obtain ⟨hy, hb', -, -⟩ := h1
        rw [hb']
        exact Int.le_trans (ctx_repBal S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn m e hp0 hy) hvc.2.2.1
      · cases h1
    · exact absurd (List.mem_of_getElem? h) (hne hr)
  · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn a r _ hm' with h | ⟨ha, hr, rp, hmr, hrp, -⟩
    · obtain ⟨c1, c2, c3, c4⟩ := q2 a r m h
      refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
      · obtain ⟨v, hv⟩ := c1; exact ⟨v, hH.ev_old hv⟩
      · obtain ⟨d1, v, d2, d3⟩ := c2 hs; exact ⟨d1, v, hH.ev_old d2, d3⟩
      · obtain ⟨v, d2, d3⟩ := c3 hs; exact ⟨v, hH.ev_old d2, d3⟩
      · obtain ⟨v, d2, d3⟩ := c4 hs; exact ⟨v, (hcv _ _).mpr d2, d3⟩
    · simp only [Msg.preAcceptReply.injEq] at hmr; subst m; subst a; subst r
      obtain ⟨hx', hb, h | ⟨seq, deps, st, hvc, e1, e2, e3, e4, hvE, -⟩⟩ := ctx_rpok S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn rp hrp
      · obtain ⟨e1, e2, e3, e4, e5, -, hw0⟩ := h
        refine ⟨⟨_, by rw [hx', hb]; exact hH.ev_old hph⟩, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
        · rw [e4] at hs; exact absurd e5 (by rw [isPA_not_ge hs]; decide)
        · rw [e4] at hs
          have := hS.2.recVote i hi x w0 hw0 (Or.inr hs)
          rw [hs] at this
          exact ⟨_, by rw [hx', e1]; exact hH.ev_old this, by rw [e2]; rfl, by rw [e3]; rfl⟩
        · rw [e4] at hs
          obtain ⟨-, hc⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 i hi x w0 hw0 hs
          exact ⟨_, by rw [hx']; exact (hcv _ _).mpr hc, by rw [e2]; rfl, by rw [e3]; rfl⟩
      · have hpa : isPA st := hvc.1
        refine ⟨⟨_, by rw [hx', hb]; exact hH.ev_old hph⟩, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
        · refine ⟨by rw [e1, hb], ⟨p.command, seq, deps⟩, ?_, by rw [e2], by rw [e3]⟩
          rw [hx', hb, e4]; exact hH.ev_new hvE
        · rw [e4] at hs; rw [hs] at hpa; exact absurd hpa acc_not_pa
        · rw [e4] at hs; exact absurd hpa (comm_not_pa hs)
  · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn a r _ hm' with h | ⟨-, -, rp, h, -⟩
    · rcases q3 a r m h with ⟨v, hv⟩ | ⟨⟨b, v, hv⟩, c2⟩
      · exact Or.inl ⟨v, hH.evBefore_old hv⟩
      · refine Or.inr ⟨⟨b, v, hH.evBefore_old hv⟩, fun m' e' hp hy hb => ?_⟩
        obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn a m' e' hp
        have hsent : S.ev a (.sent r (.acceptReply m)) := by
          obtain ⟨pp, pp', hlt, h0, h1⟩ := hv; exact List.mem_of_getElem? h1
        exact c2 m' e' hp0 hy (hH.evBefore_back hb hsent (fun _ => ctx_notE S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (by simp [newKind]) rfl))
    · cases h

theorem ctx_hi : Inv.prepReplyHighest S' := by
  intro r m e hp b st v hb
  obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r m e hp
  exact hS.1.2.2.2.2.2.2.2.2.2.1 r m e hp0 b st v (hH.evBefore_back hb hp0.1 hne)

theorem ctx_lb : Inv.lbInv S' := by
  obtain ⟨-, -, -, hmk, hxq, -, -, -, -, hfi, -, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨-, hlbeq, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hX := ctx_X S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro r hr y w lb hw hlb
  obtain ⟨w0', hw0', hrel⟩ : ∃ w0', (S.rep r).inst y = some w0' ∧
      ((w0' = w ∧ (r ≠ i ∨ y ≠ x)) ∨ (r = i ∧ y = x ∧ w0' = w0 ∧ w = w')) := by
    rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w
      rcases hro with h | ⟨h, rfl⟩
      · exact ⟨w0, h, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
      · rw [hlbeq] at hlb; simp [newInstanceDefault] at hlb
    · by_cases hc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hc
        rw [R3] at hw; cases hw
        rcases hro with h' | ⟨h', rfl⟩
        · exact ⟨w0, h', Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
        · rw [hlbeq] at hlb; simp [newInstanceDefault] at hlb
      · exact ⟨w, h, Or.inl ⟨rfl, by
          by_cases h1 : r = i
          · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
          · exact Or.inl h1⟩⟩
  have hlb0 : w0'.lb = some lb := by
    rcases hrel with ⟨rfl, -⟩ | ⟨-, -, rfl, rfl⟩
    · exact hlb
    · rw [← hlbeq]; exact hlb
  obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
    hS.1.2.2.2.2.2.2.2.2.2.2.1 r hr y w0' lb hw0' hlb0
  refine ⟨hH.ev_old a1, a2, a3, fun b v hv => a4 b v ?_, fun c1 c2 => ?_, ⟨Q, q1, q2, ?_⟩,
    ⟨Q', q1', q2', ?_⟩, fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
  · rcases hv with hv | hv
    · exact Or.inl (hold r _ hv (by simp [newKind]))
    · exact Or.inr (hold r _ hv (by simp [newKind]))
  · obtain ⟨d1, d2, v, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, v, hH.ev_old d3, d4⟩
  · intro a m' h; obtain ⟨b1, b2, b3, b4⟩ := q3 a m' h; exact ⟨b1, b2, hH.deliveredMsg_old b3, b4⟩
  · intro a h; obtain ⟨b1, b2, m', b3, b4⟩ := q3' a h
    exact ⟨b1, b2, m', hH.deliveredMsg_old b3, b4⟩
  · rcases hrel with ⟨rfl, -⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
    · rcases hX with ⟨-, he⟩ | ⟨h, -⟩ | ⟨-, he, -, -⟩ | ⟨seq, deps, st, hvc, -⟩
      · rw [he] at c2 c3; obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
      · rw [h] at hw0'; cases hw0'
      · exfalso
        rw [he] at c3; simp only at c3
        rw [← c3] at a1
        exact hfi (maker_eq S hS.1.2.2.2.2.2.1 hxq hmk a1)
      · exfalso; rw [hvc.2.1] at c2; simp only [paRec] at c2
        rcases hvc.1 with h | h <;> rw [h] at c2 <;> exact absurd c2 (by decide)
  · obtain ⟨c1, c2⟩ := a9 hp
    refine ⟨c1, fun e he => ?_⟩
    obtain ⟨d1, d2, d3⟩ := c2 e he
    refine ⟨d1, d2, ?_⟩
    rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, hH.deliveredMsg_old e2⟩
    · exact Or.inr ⟨e1, hH.ev_old e2⟩

theorem ctx_agr : Inv.agreement S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun y v v' h h' => hS.1.2.2.2.2.2.2.2.2.2.2.2.1.1 y v v' ((hcv _ _).mp h)
    ((hcv _ _).mp h'), fun r hr y w hw hc => ?_⟩
  obtain ⟨w1, w2, h1, h2, e1, e2, e3, e4, -⟩ := ctx_view S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y (Or.inr ⟨w, hw, Or.inl hc⟩)
  rw [hw] at h2; cases h2
  rw [e1] at hc
  obtain ⟨c1, c2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 r hr y w1 h1 hc
  refine ⟨by rw [e2]; exact c1, (hcv _ _).mpr ?_⟩
  simp only [instVal, e2, e3, e4]; exact c2

theorem ctx_dc : Inv.decidedChosen S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro y v hv
  rcases hS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 y v ((hcv _ _).mp hv) with ⟨b, Q, h1, h2, h3⟩ | ⟨⟨Q, h1, h2, h3⟩, hf⟩
  · exact Or.inl ⟨b, Q, h1, h2, fun r hr => ⟨(h3 r hr).1, hH.ev_old (h3 r hr).2⟩⟩
  · refine Or.inr ⟨⟨Q, h1, h2, fun r hr => ?_⟩, hH.ev_old hf⟩
    obtain ⟨c1, c2, st, c3, c4⟩ := h3 r hr
    exact ⟨c1, c2, st, c3, hH.ev_old c4⟩

theorem ctx_dcv : Inv.depsCover S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro y z vy vz hyz hy hz hi'
  exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y z vy vz hyz ((hcv _ _).mp hy) ((hcv _ _).mp hz) hi'

theorem ctx_wit : Inv.witnesses S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro y v hv hn'
  obtain ⟨W, w1, w2, w3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y v ((hcv _ _).mp hv) hn'
  exact ⟨W, w1, w2, fun r hr => by
    obtain ⟨c1, d, c2, c3⟩ := w3 r hr; exact ⟨c1, d, hH.ev_old c2, c3⟩⟩

/-- The new attribute computation covers what `i` recorded before. -/
theorem ctx_ac : Inv.attrsCover S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdeps, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro r e y cy z cz d hrec hyz hb hint
  rcases (hH.evBefore_iff _ _ _ _).mp hb with h | ⟨he, hr, h⟩ | ⟨hr, -, pp, pp', -, h1, h2⟩
  · exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r e y cy z cz d hrec hyz h hint
  · subst r
    rcases ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ h with ⟨rp, h1, -⟩ | ⟨seq, deps, st, hvc, h1 | h1⟩
    · cases h1
    · cases h1
    · simp only [Event.attrsRec.injEq] at h1; obtain ⟨hz, hcz, hdz⟩ := h1
      subst z; subst cz; subst d
      obtain ⟨-, -, -, -, σu, hu, hd, hus, hup⟩ := hvc
      obtain ⟨c, hc, c', hc', hint⟩ := hint
      have hyq : y.q < nR := (hS.2.crtEv i e y he (by
        cases e <;> simp_all [Event.recorded, Event.instOf])).1
      obtain ⟨u1, -, u3, -⟩ := ua_spec σu p.command p.seq p.deps
      have hlen : p.deps.length = nR := hdeps.1
      unfold covers
      rw [hd, getD_irrel _ _ _ (W32 0) (by rw [u1, hlen]; exact hyq)]
      rcases hint with ⟨hk, hop⟩ | ⟨hs, hpt⟩ | ⟨hpt, hs⟩
      · -- the key clause: the conflicts map (`confCover`)
        obtain ⟨pe, hpe, hl, hlw⟩ := hS.2.confCover i hi e y cy he hrec c' hc'
        have hcov := (u3 hlen y.q hyq c hc).1 pe (by rw [hu, hk]; exact hpe)
        refine Int.le_trans ?_ hcov
        unfold uaD
        by_cases hg : c.op ≠ opGET
        · rw [if_pos hg]; exact hl
        · rw [if_neg hg]
          exact hlw (by rcases hop with h | h; exact absurd h hg; exact h)
      · -- a SCAN against a recorded PUT: the row's last PUT (`classCover`, fix S1)
        have hcov := (u3 hlen y.q hyq c hc).2
        have hcl := (hS.2.classCover i hi e y cy he hrec c' hc').2 hpt
        refine Int.le_trans hcl (Int.le_trans (Int.le_of_eq ?_) hcov)
        simp only [uaClass, if_pos hs, hup]
      · -- a PUT against a recorded SCAN: the row's last SCAN
        have hcov := (u3 hlen y.q hyq c hc).2
        have hcl := (hS.2.classCover i hi e y cy he hrec c' hc').1 hs
        refine Int.le_trans hcl (Int.le_trans (Int.le_of_eq ?_) hcov)
        have hns : c.op ≠ opSCAN := by rw [hpt]; decide
        simp only [uaClass, if_neg hns, if_pos hpt, hus]
  · subst r
    have he1 := ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (List.mem_of_getElem? h1)
    have he2 := ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (List.mem_of_getElem? h2)
    rcases he1 with ⟨rp, rfl, -⟩ | ⟨seq, deps, st, -, rfl | rfl⟩
    · simp [Event.recorded] at hrec
    · simp [Event.recorded] at hrec
    · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
      obtain ⟨rfl, -⟩ := hrec
      rcases he2 with ⟨rp, h3, -⟩ | ⟨seq', deps', st', hvc', h3 | h3⟩
      · cases h3
      · cases h3
      · simp only [Event.attrsRec.injEq] at h3; exact absurd h3.1.symm hyz

theorem ctx_exec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧ Inv.execPrefix S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hex := ctx_executed S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hview := ctx_view S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr
    refine ⟨by rw [hH.execLog]; exact e1, fun y => by rw [hH.execLog, hex]; exact e2 y,
      fun y w hw hs => ?_⟩
    obtain ⟨w1, w2, h1, h2, f1, f2, f3, f4, -⟩ := hview r y (Or.inr ⟨w, hw, Or.inr hs⟩)
    rw [hw] at h2; cases h2
    rw [f1] at hs
    obtain ⟨c1, c2⟩ := e3 y w1 h1 hs
    refine ⟨(hcv _ _).mpr (by simp only [instVal, f2, f3, f4]; exact c1), fun z hz => ?_⟩
    obtain ⟨w3, hw3, hz1, hz2⟩ := hz
    rw [hw] at hw3; cases hw3
    rw [hex, hH.execCur]; exact c2 z ⟨w1, h1, hz1, by rw [← f4]; exact hz2⟩
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
        refine slotsOn_congr' _ _ _ k (fun y hy => ?_)
        have hey : (S.rep i).executed y :=
          ((hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi).2.1 y).mp hy
        obtain ⟨w, hw, hs⟩ := hey
        obtain ⟨w1, w2, h1, h2, -, f2, -⟩ := hview i y (Or.inl ⟨w, hw, Or.inr hs⟩)
        rw [h1, h2]; simp [f2]
      · simp only [Sys.lexec, Sys.curSlots, hH.execCur, hH.execLog, hH.execIdx, hH.rep_other hri]
    obtain ⟨p1, p2, p3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
    · rw [hlx, hH.gexec]; exact p1 r hr k
    · rw [hlx, (ctx_fields S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r).2.2.2.1]; exact p2 r hr k
    · rw [hlx] at h; rw [hH.gexec]; exact p3 r hr k pre e post h

theorem ctx_slots : Inv.slots S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨s1, s2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun y v hv => ?_, fun y ps h => ?_⟩
  · rw [hH.owner]; exact s1 y v ((hcv _ _).mp hv)
  · rw [hH.owner] at h; rw [hH.ops]; exact s2 y ps h

theorem ctx_co : Inv.clientOps S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hso : S'.slotOp = S.slotOp := by funext sl; simp only [Sys.slotOp, hH.owner]
  have := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [Inv.clientOps, hso, hH.gexec, hH.fired, hH.ops, hcv] at this ⊢
  exact this

theorem ctx_cm : Inv.commitMsgs S' := by
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to _ hm' with h | ⟨-, -, rp, h, -⟩
  · obtain ⟨r, b, h1⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 fr' to m h
    exact ⟨r, b, hH.ev_old h1⟩
  · cases h

theorem ctx_pk : Inv.pendingKind S' := by
  intro r b hb
  rw [hH.pending] at hb
  by_cases hri : r = i
  · subst r; simp at hb
  · rw [upd_other _ _ _ _ hri] at hb
    exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r b hb

theorem ctx_mono : SafeMono S S' := by
  obtain ⟨hpm, -, -, hmk, hxq, -, -, -, -, -, -, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, -, -, -, -, -, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hX := ctx_X S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r y w hw => ?_, fun r e he => hH.ev_old he, fun r y b st v he => ?_,
    fun y v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ _ he (by simp [newKind])),
    fun a y m hm' _ _ => ?_⟩
  · rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w
      refine ⟨w', R3, hwb, fun hs => Or.inl ?_⟩
      rcases hX with ⟨-, he⟩ | ⟨h, -⟩ | ⟨-, he, -⟩ | ⟨seq, deps, st, hvc, -⟩
      · rw [he]; exact hs
      · rw [h] at hw; cases hw
      · rw [he]; exact hs
      · rw [hvc.2.2.2.1] at hs; cases hs
    · exact ⟨w, h, Int.le_refl _, fun hs => Or.inl hs⟩
  · rcases ctx_vote S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b st v he with h | ⟨hr, hy, hb', seq, deps, hvc, hv, -⟩
    · exact Or.inl h
    · subst r; subst y; subst b; subst v
      refine Or.inr ⟨fun w hw => ?_, fun _ st' u hst' hu => ?_, fun _ hb hq => ?_⟩
      · rcases hro with h' | ⟨h', -⟩
        · rw [h'] at hw; cases hw; exact ⟨hvc.2.2.1, fun _ _ => hvc.2.2.2.1⟩
        · rw [h'] at hw; cases hw
      · exact absurd hu (ctx_novb S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn seq deps st hvc st' u (Or.inl hst'))
      · -- the PreAccept at the initial ballot is from the leader
        have hfq : fr = x.q := by
          rcases (hS.1.2.2.2.2.2.1.1 fr x _ hmk).1 with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · rw [hb, zz_initBal x hxq] at h; simp [nR] at h hxq; omega
        subst hfq
        exact ⟨p, hpm, by rw [hx]; rfl, hb⟩
  · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn y.q a _ hm' with h | ⟨-, -, rp, h, -⟩
    · exact Or.inl h
    · cases h

theorem ctx_safe : Inv.safe S' :=
  safe_frame (ctx_mono S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn)
    hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun r y b v he => ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he (by simp [newKind]))
    (fun r y b v he => ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ he (by simp [newKind]))

theorem ctx_reports : Inv.reports S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrepo⟩ :=
    hS.1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hrepo
  have hmo := ctx_mono S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hP := ctx_prep S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  refine ⟨fun r m e hp => c1 r m e (hP r m e hp).1, fun r m e hp => c2 r m e (hP r m e hp).1,
    fun r m e hp => c3 r m e (hP r m e hp).1, fun r m e hp b u hb => ?_, fun r m e hr hp => ?_,
    fun r y b st st' v v' h1 h2 h3 h4 => ?_, fun y v m e h1 h2 h3 => ?_,
    fun r y v h1 w => ?_, fun r m e hp => c9 r m e (hP r m e hp).1⟩
  · obtain ⟨hp0, hne⟩ := hP r m e hp
    exact c4 r m e hp0 b u (hH.evBefore_back hb hp0.1 hne)
  · obtain ⟨w, hw, hle⟩ := c5 r m e hr (hP r m e hp).1
    obtain ⟨w', hw', hle', -⟩ := hmo.bal r _ w hw
    exact ⟨w', hw', Int.le_trans hle hle'⟩
  · rcases ctx_vote S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b st v h3 with h | ⟨hr, hy, hb, seq, deps, hvc, hv, -⟩ <;>
      rcases ctx_vote S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r y b st' v' h4 with h' | ⟨hr', hy', hb', seq', deps', hvc', hv', -⟩
    · exact c6 r y b st st' v v' h1 h2 h h'
    · subst r; subst y; subst b; exact absurd h (ctx_novb S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn seq' deps' st' hvc' st v (Or.inl h1))
    · subst r; subst y; subst b; exact absurd h' (ctx_novb S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn seq deps st hvc st' v' (Or.inl h2))
    · subst v; subst v'
      have e := hvc'.2.1
      rw [hvc.2.1] at e
      have e1 : seq = seq' := by simpa [paRec] using congrArg InstRec.seq e
      have e2 : deps = deps' := by simpa [paRec] using congrArg InstRec.deps e
      rw [e1, e2]
  · exact c7 y v m e (ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ _ h1 (by simp [newKind])) (hP _ m e h2).1 h3
  · exact fastBlocked_mono hmo (c8 r y v (ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r _ h1 (by simp [newKind])) w)

end

/-- A handler step of an idle replica appends its direct sends to its outbox. -/
private theorem pa_outbox_eq {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {snd : Nat → List Msg} (hH : HS S S' i σ' E snd none) (hidle : S.pending i = none)
    (fr to : Nat) : S'.outbox fr to = S.outbox fr to ++ (if fr = i then snd to else []) := by
  have h1 := hH.msgs fr to
  simp only [Sys.msgs, Sys.intended, hH.sent, hH.pending] at h1
  by_cases hf : fr = i
  · subst hf
    simp only [upd_same, hidle, if_true, intendedOf, List.append_nil, List.append_assoc] at h1 ⊢
    exact List.append_cancel_left h1
  · simp only [upd_other _ _ _ _ hf, hf, if_false, List.append_nil, List.append_assoc] at h1 ⊢
    exact List.append_cancel_right (List.append_cancel_left h1)

section
variable (S S' : Sys) (fr i n : Nat) (p : PreAccept) (x : InstId) (w0 w' : InstRec) (σ' : RState)
  (E : List Event) (snd : Nat → List Msg)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.preAccept p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i σ' E snd none)
  (hid : σ'.id = (S.rep i).id) (hpo : σ'.peerOrder = (S.rep i).peerOrder)
  (hcrt : σ'.crtInstance = (bumpCrt (S.rep i) x.q p.inst).crtInstance)
  (hexe : σ'.execedUpTo = (S.rep i).execedUpTo) (hsto : σ'.store = (S.rep i).store)
  (hσi : σ'.inst = upd (S.rep i).inst x (some w'))
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ (∀ to, snd to = []) ∧ σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd, w' = { w0 with bal := p.ballot } ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = true ∧
         E = [.sent fr (.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p w0.vbal w0.seq w0.deps cd w0.status)] else []) ∧
         σ'.conflicts = (S.rep i).conflicts ∧
         σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) ∨
       (∃ cd seq deps st, ∃ σu : RState, σu.conflicts = (S.rep i).conflicts ∧
         deps = (updateAttributes σu p.command p.seq p.deps).2.1 ∧
         (st = stPREACCEPTED ∨ st = stPREACCEPTED_EQ) ∧
         w' = paRec w0 p seq deps st ∧ zz w0.bal ≤ zz p.ballot ∧
         stGe w0.status stACCEPTED = false ∧
         E = [.vote x p.ballot st ⟨p.command, seq, deps⟩, .attrsRec x p.command deps,
              .sent fr (.preAcceptReply (paRep p p.ballot seq deps cd st))] ∧
         (∀ to, snd to = if to = fr then
           [.preAcceptReply (paRep p p.ballot seq deps cd st)] else []) ∧
         ∃ σb : RState, σb.conflicts = (S.rep i).conflicts ∧
           σ'.conflicts = (updateConflicts σb p.command x.q p.inst p.seq).conflicts ∧
           σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut ∧
           σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
           σb.inst = σ'.inst ∧
           σ'.lastScan = (updateConflicts σb p.command x.q p.inst p.seq).lastScan ∧
           σ'.lastPut = (updateConflicts σb p.command x.q p.inst p.seq).lastPut))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn

/-- Every PreAccept at the step's ballot to `i` is delivered after the step. -/
theorem ctx_allDeliv : ∀ fr', S'.allDeliv fr' i (Msg.isPAat x p.ballot) := by
  obtain ⟨hpm, -, hph, hmk, hxq, -, -, -, -, hfi, -, -⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  intro fr' n' m hn' hp
  have hmem : m ∈ S'.msgs fr' i := List.mem_of_getElem? hn'
  rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' i m hmem with h | ⟨-, hto, rp, rfl, -⟩
  · cases m with
    | preAccept m' =>
      simp only [Msg.isPAat, decide_eq_true_eq] at hp
      obtain ⟨hy, hb⟩ := hp
      obtain ⟨-, hph'⟩ := hS.1.2.2.2.2.2.1.2.2.2.2.1 fr' i m' h
      rw [hy, hb] at hph'
      have hff : fr' = fr := (hS.1.2.2.2.2.2.2.1.1 fr' fr x p.ballot _ _ hph' hph).1
      subst fr'
      rw [hH.msgs, if_neg hfi, List.append_nil] at hn'
      have := pos_unique _ _ (hS.2.paMsgOnce fr i x p.ballot) hn' (by simp [Msg.isPAat, hy, hb])
        (msgs_of_sent S hm) (by simp [Msg.isPAat, hx])
      rw [this]; exact hdn
    | _ => simp [Msg.isPAat] at hp
  · exact absurd hto.symm hfi

/-- The reply handlers' conjuncts after the step. -/
theorem ctx_pm : InvPM S' := by
  obtain ⟨hpm, hldr, hph, hmk, hxq, hxi, hpi0, hpi, hb0, hfi, hdeps, hcne⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, hlbeq, -, -, -, -, -⟩ := ctx_w S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hA := hS.2
  have hP := hA.pm
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hvo := ctx_vote S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have CM := ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have RP := ctx_rpok S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hown := hS.1.2.2.2.2.2.1
  have hop := hS.1.2.2.2.2.2.2.1
  have hagr := hS.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
  have hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v) :=
    fun r y b v h => hold r _ h (by simp [newKind])
  have hph' : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v) :=
    fun r y b v h => hold r _ h (by simp [newKind])
  have hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
    fun r y c u h => hold r _ h (by simp [newKind])
  have hsent : ∀ fr' to m, m ∈ S.sent fr' to → m ∈ S'.sent fr' to :=
    fun _ _ _ h => by rw [hH.sent]; exact h
  have hcv : ∀ y u, S.committedVal y u → S'.committedVal y u := fun y u h =>
    (ctx_cv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn y u).mpr h
  have hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w.bal ≤ zz w2.bal := by
    intro r y w hw
    rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w; exact ⟨w', R3, hwb⟩
    · exact ⟨w, h, Int.le_refl _⟩
  have hlb0 : ∀ r y w2 lb, (S'.rep r).inst y = some w2 → w2.lb = some lb →
      ∃ w1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb := by
    intro r y w2 lb hw hl
    rcases R1 r y w2 hw with ⟨h1, h2, h3⟩ | h
    · subst r y w2
      rw [hlbeq] at hl
      rcases hro with h | ⟨-, h⟩
      · exact ⟨w0, h, hl⟩
      · rw [h] at hl; simp [newInstanceDefault] at hl
    · exact ⟨w2, h, hl⟩
  have hlb : ∀ r y w2 lb', (S'.rep r).inst y = some w2 → w2.lb = some lb' →
      ∃ w1 lb, (S.rep r).inst y = some w1 ∧ w1.lb = some lb ∧ PMProof.LbPM lb lb' := by
    intro r y w2 lb' hw hl
    obtain ⟨w1, h1, h2⟩ := hlb0 r y w2 lb' hw hl
    exact ⟨w1, lb', h1, h2, PMProof.LbPM.refl _⟩
  have hPAR : ∀ fr' to (m : Msg), m ∈ S'.msgs fr' to → (∀ rp, m ≠ .preAcceptReply rp) →
      m ∈ S.msgs fr' to := by
    intro fr' to m h hne
    rcases CM fr' to m h with h | ⟨-, -, rp, rfl, -⟩
    · exact h
    · exact absurd rfl (hne rp)
  have hnewrep : ∀ a r rp, Msg.preAcceptReply rp ∈ S'.msgs a r →
      Msg.preAcceptReply rp ∈ S.msgs a r ∨ (a = i ∧ r = fr ∧ RPok S i fr p x w0 w' E rp) := by
    intro a r rp h
    rcases CM a r _ h with h | ⟨h1, h2, rp', he, hrp, -⟩
    · exact Or.inl h
    · simp only [Msg.preAcceptReply.injEq] at he; subst he; exact Or.inr ⟨h1, h2, hrp⟩
  have hpS : Msg.preAccept p ∈ S'.sent fr i := by rw [hH.sent]; exact List.mem_of_getElem? hm
  have hpx : (⟨toN p.replica, toN p.inst⟩ : InstId) = x := hx.symm
  have hgeNone : ∀ {s : w8}, stGe s stACCEPTED = true → s ≠ stNONE := by
    intro s h h'; subst h'; simp [stGe, stNONE, stACCEPTED] at h
  -- parCom
  have hparCom : ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S'.msgs a r →
      isCommitted m.status → ∃ c u, S'.ev a (.commit (parX m) c u) ∧ zz c ≤ zz m.ballot ∧
        u.seq = m.seq ∧ u.deps = m.deps := by
    intro a r m hm' hc
    rcases hnewrep a r m hm' with h | ⟨ha, hr, hrp⟩
    · obtain ⟨c, u, h1, h2, h3, h4⟩ := hP.parCom a r m h hc
      exact ⟨c, u, hmono _ _ h1, h2, h3, h4⟩
    · subst a r
      obtain ⟨hx', hb', h | ⟨seq, deps, st, hvc, -, -, -, e4, -⟩⟩ := RP m hrp
      · obtain ⟨-, e2, e3, e4, -, e6, hw0⟩ := h
        rw [e4] at hc
        obtain ⟨c, u, h1, h2⟩ := hA.recCommit i hi x w0 hw0 hc
        obtain ⟨-, hcv0⟩ := hagr.2 i hi x w0 hw0 hc
        have hu := hagr.1 x u (instVal w0) (Or.inl ⟨i, c, h1⟩) hcv0
        rw [e6] at hwb
        refine ⟨c, u, ?_, ?_, ?_, ?_⟩
        · show S'.ev i (.commit ⟨toN m.replica, toN m.inst⟩ c u); rw [hx']; exact hmono _ _ h1
        · rw [hb']; exact Int.le_trans h2 hwb
        · rw [hu, e2]; rfl
        · rw [hu, e3]; rfl
      · rw [e4] at hc; exact absurd hvc.1 (comm_not_pa hc)
  -- parSt
  have hparSt : ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S'.msgs a r →
      (isPA m.status ∨ m.status = stACCEPTED ∨ isCommitted m.status) ∧ 0 ≤ zz m.vballot ∧
      zz m.vballot ≤ zz m.ballot ∧ ∃ p : PreAccept, Msg.preAccept p ∈ S'.sent r a ∧
        (⟨toN p.replica, toN p.inst⟩ : InstId) = parX m ∧ p.ballot = m.ballot := by
    intro a r m hm'
    rcases hnewrep a r m hm' with h | ⟨ha, hr, hrp⟩
    · obtain ⟨h1, h2, h3, p', h4, h5, h6⟩ := hP.parSt a r m h
      exact ⟨h1, h2, h3, p', hsent _ _ _ h4, h5, h6⟩
    · subst a r
      obtain ⟨hx', hb', h | ⟨seq, deps, st, hvc, e1, -, -, e4, -⟩⟩ := RP m hrp
      · obtain ⟨e1, -, -, e4, e5, e6, hw0⟩ := h
        have hne : w0.status ≠ stNONE := hgeNone e5
        rw [e6] at hwb
        refine ⟨?_, ?_, ?_, p, hpS, by rw [hpx]; exact hx'.symm, hb'.symm⟩
        · rw [e4]
          rcases hA.stRange i hi x w0 hw0 with h | h | h | h
          · exact absurd h hne
          · rw [isPA_not_ge h] at e5; cases e5
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        · rw [e1]; exact hA.vbalNonneg i hi x w0 hw0 hne
        · rw [e1, hb']; exact Int.le_trans (hS.1.2.2.2.2.1.1 i hi x w0 hw0) hwb
      · rw [e4, e1, hb']
        exact ⟨Or.inl hvc.1, hb0, Int.le_refl _, p, hpS, by rw [hpx]; exact hx'.symm, rfl⟩
  -- paSent
  have hpend : ∀ r b, S'.pending r = some b → b.trackPA = true → S.pending r = some b := by
    intro r b hb _
    rw [hH.pending] at hb
    by_cases hr : r = i
    · subst hr; rw [upd_same] at hb; cases hb
    · rwa [upd_other _ _ _ _ hr] at hb
  have hrc : ∀ (y : InstId) a, (S'.sent y.q a ++ S'.outbox y.q a).any (Msg.isPAat y (initBal y)) = true →
      (S.sent y.q a ++ S.outbox y.q a).any (Msg.isPAat y (initBal y)) = true := by
    intro y a h
    obtain ⟨m, hm', hpa⟩ := List.any_eq_true.mp h
    rw [hH.sent, pa_outbox_eq hH hidle.1] at hm'
    refine List.any_eq_true.mpr ⟨m, ?_, hpa⟩
    simp only [List.mem_append] at hm' ⊢
    rcases hm' with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · split at h
      · obtain ⟨-, rp, rfl, -⟩ := ctx_snd S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn a m h
        simp [Msg.isPAat] at hpa
      · cases h
  have hpaSent := PMProof.ps_frame hP (fun y w2 lb hw hl => by
      obtain ⟨w1, h1, h2⟩ := hlb0 _ y w2 lb hw hl
      exact ⟨w1, lb, h1, h2, rfl, rfl⟩) hpend hrc
  -- pendPA
  have hpendPA : ∀ r b, S'.pending r = some b → ∀ y c, b.m.isPAat y c = true →
      b.trackPA = true ∧ b.x = y := by
    intro r b hb y c hc
    rw [hH.pending] at hb
    by_cases hr : r = i
    · subst hr; rw [upd_same] at hb; cases hb
    · rw [upd_other _ _ _ _ hr] at hb; exact hP.pendPA r b hb y c hc
  -- paVoteMsg
  have hpaVoteMsg : ∀ r y st v, isPA st → r ≠ y.q → S'.ev r (.vote y (initBal y) st v) →
      ∃ p : PreAccept, Msg.preAccept p ∈ S'.sent y.q r ∧
        (⟨toN p.replica, toN p.inst⟩ : InstId) = y ∧ p.ballot = initBal y := by
    intro r y st v hst hne hv
    rcases hvo r y _ st v hv with h | ⟨hr, hy, hb, -⟩
    · obtain ⟨p', h1, h2, h3⟩ := hP.paVoteMsg r y st v hst hne h
      exact ⟨p', hsent _ _ _ h1, h2, h3⟩
    · subst r y
      have hfq : fr = x.q := by
        rcases (hown.1 fr x p.ballot hmk).1 with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact h2
        · exfalso; rw [← hb, zz_initBal x hxq] at h1; omega
      rw [← hfq]; exact ⟨p, hpS, hpx, hb.symm⟩
  -- parNoPA
  have hparNoPA : ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S'.msgs a r →
      ¬ isPA m.status → ∀ st u, isPA st → ¬ S'.ev a (.vote (parX m) m.ballot st u) := by
    intro a r m hm' hnp st u hst hv
    rcases hnewrep a r m hm' with hm0 | ⟨ha, hr, hrp⟩
    · rcases hvo a _ _ st u hv with h | ⟨ha, hy, hb, -⟩
      · exact hP.parNoPA a r m hm0 hnp st u hst h
      · subst a
        obtain ⟨-, -, -, p', hp', hpx', hpb⟩ := hP.parSt i r m hm0
        have hph2 := (hown.2.2.2.2.1 r i p' (by simp only [Sys.msgs, List.mem_append]; exact Or.inl (Or.inl hp'))).2
        rw [hpx', hy, hpb, hb] at hph2
        have hrf : r = fr := (hop.1 r fr x p.ballot _ _ hph2 hph).1
        subst r
        have hc : 1 ≤ S.cnt i fr (Msg.isPARat x p.ballot) :=
          List.length_pos_of_mem (List.mem_filter.mpr ⟨hm0, decide_eq_true ⟨hy, hb⟩⟩)
        exact hn ((hA.parOnce i fr x p.ballot hc).2 n _ (msgs_of_sent S hm) (by simp [Msg.isPAat, hx]))
    · subst a r
      obtain ⟨hx', hb', h | ⟨seq, deps, st', hvc, -, -, -, e4, -⟩⟩ := RP m hrp
      · obtain ⟨-, -, -, -, e5, -, -⟩ := h
        have hv' : S'.ev i (.vote x p.ballot st u) := by
          rw [← hx', ← hb']; exact hv
        rcases hvo i x p.ballot st u hv' with h | ⟨-, -, -, seq, deps, hvc, -⟩
        · rcases hA.paVoteDeliv i x p.ballot st u hst h with ⟨v0, h0⟩ | h0
          · exact hfi (hop.1 fr i x p.ballot _ v0 hph h0).1
          · exact hn (h0 fr n _ (msgs_of_sent S hm) (by simp [Msg.isPAat, hx]))
        · rw [hvc.2.2.2.1] at e5; cases e5
      · exact hnp (by rw [e4]; exact hvc.1)
  -- paGe
  have hpaGe : ∀ r y b st v ℓ v0, isPA st → S'.ev r (.vote y b st v) → S'.ev ℓ (.phase1 y b v0) →
      depsLe v0.deps v.deps := by
    intro r y b st v ℓ v0 hst hv hp0
    have hp0' := hph' _ _ _ _ hp0
    rcases hvo r y b st v hv with h | ⟨hr, hy, hb, seq, deps, hvc, hv', -⟩
    · exact hP.paGe r y b st v ℓ v0 hst h hp0'
    · subst r y b v
      have := (hop.1 ℓ fr x p.ballot v0 _ hp0' hph).2.1
      subst this
      obtain ⟨-, -, -, -, σu, -, hd, -⟩ := hvc
      obtain ⟨u1, u2, -, -⟩ := ua_spec σu p.command p.seq p.deps
      refine ⟨hdeps.1, ?_, fun q _ => ?_⟩
      · show deps.length = nR; rw [hd, u1]; exact hdeps.1
      · show zz (p.deps.getD q 0) ≤ zz (deps.getD q 0); rw [hd]; exact u2 q
  exact {
    arOk := PMProof.arOk_frame hP (fun a r m h => hPAR a r _ h (fun _ h => by cases h)) hacc
      (fun q y b v h => by
        rcases hvo q y b _ v h with h | ⟨-, -, -, seq, deps, hvc, -⟩
        · exact Or.inl h
        · exfalso; rcases hvc.1 with h | h <;> exact absurd h (by decide)) hmono hcv hbal
    commitProp := PMProof.commitProp_frame hP hcm hmono
    commitMsgProp := PMProof.commitMsgProp_frame hP
      (fun a r m h => hPAR a r _ h (fun _ h => by cases h)) hmono
    lbProp := PMProof.lbProp_frame hP hlb hacc hmono
    parCom := hparCom
    parSt := hparSt
    paFresh := PMProof.paFresh_frame hP hlb hph'
    paCmds := PMProof.paCmds_frame hP hlb hph'
    paSent := hpaSent
    pendPA := hpendPA
    paVoteMsg := hpaVoteMsg
    parNoPA := hparNoPA
    aeF := PMProof.aeF_frame hP hlb hsent
    repLead := PMProof.repLead_frame hP (fun r m e h => (ctx_prep S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r m e h).1) hbal
    paGe := hpaGe
    phAttrs := PMProof.phAttrs_frame hP hph' hmono
    accWit := PMProof.accWit_frame hP hacc hmono hcv
    accVote := PMProof.accVote_frame hP hacc hmono
    cmdSafe := CmdSafeProof.cmdSafe_frame hP (ctx_mono S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn) hph'
    accSup := CmdSafeProof.accSup_frame hP hmono hacc }

theorem ctx_aux (hchan : S'.proposeChan = S.proposeChan) : InvAux S' := by
  obtain ⟨hpm, hldr, hph, hmk, hxq, hxi, hpi0, hpi, hb0, hfi, hdeps, hcne⟩ := ctx_basic S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hwb, hlbeq, hid', hvb, hbal', hst', hcw⟩ := ctx_w S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨hrange0, hvb0, hid0⟩ := ctx_w0 S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hA := hS.2
  have hold := ctx_ev_old S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hX := ctx_X S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have F := ctx_fields S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hcrtle := ctx_crt_le S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hvo := ctx_vote S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hview := ctx_view S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hAD := ctx_allDeliv S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hcq : ∀ q, zz ((S'.rep q).crtInstance q) = zz ((S.rep q).crtInstance q) := by
    intro q
    rw [(F q).2.2.2.2.1 q]
    split
    · rename_i hc; obtain ⟨rfl, hq⟩ := hc
      have := hA.crtMsg fr q _ x hpm (by rw [hx]; rfl)
      rw [← hq] at this; rw [← hpi] at *; omega
    · rfl
  have hnv : (S.rep i).inst x = none → ∀ b st v, ¬ S.ev i (.vote x b st v) := by
    intro h b st v hv
    obtain ⟨w, hw, -⟩ := hS.1.2.2.2.2.1.2 i hi x b st v hv
    rw [h] at hw; cases hw
  have hoth : ∀ r y w, (S'.rep r).inst y = some w → ¬ (r = i ∧ y = x) →
      (S.rep r).inst y = some w := by
    intro r y w hw hc
    rcases R1 r y w hw with ⟨h1, h2, -⟩ | h
    · exact absurd ⟨h1, h2⟩ hc
    · exact h
  have hnoP : ∀ (P : Msg → Bool), (∀ c, P (.preAcceptReply c) = false) →
      ∀ to m, m ∈ snd to ++ intendedOf none to → P m = false := by
    intro P hP to m hm'
    have : m ∈ snd to := by simpa [intendedOf] using hm'
    obtain ⟨-, c, rfl, -⟩ := ctx_snd S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn to m this
    exact hP _
  have hcnt0 : ∀ fr' to (P : Msg → Bool), (∀ c, P (.preAcceptReply c) = false) →
      S'.cnt fr' to P = S.cnt fr' to P := by
    intro fr' to P hP
    rw [hH.cnt_eq]
    split
    · rw [List.filter_eq_nil_iff.mpr (fun m hm' => by simp [hnoP P hP to m hm'])]; rfl
    · rfl
  -- the vote case's status is pre-accepted
  have hVst : ∀ seq deps st, VC S i p w0 w' seq deps st → isPA w'.status ∧ w'.vbal = p.ballot ∧
      w'.cmds = some p.command ∧ instVal w' = ⟨p.command, seq, deps⟩ ∧ w'.status = st := by
    intro seq deps st hvc
    rw [hvc.2.1]; exact ⟨hvc.1, rfl, rfl, by simp [instVal, paRec], rfl⟩
  have hpaNone : ∀ {s : w8}, isPA s → s ≠ stNONE := by
    intro s h h'; subst h'; exact none_not_pa h
  have hgeNone : ∀ {s : w8}, stGe s stACCEPTED = true → s ≠ stNONE := by
    intro s h h'; subst h'; simp [stGe, stNONE, stACCEPTED] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- stRange
    intro r hr y w hw
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with ⟨h, he⟩ | ⟨-, he, -⟩ | ⟨h, he, -⟩ | ⟨seq, deps, st, hvc, -⟩
      · rw [he]; exact hA.stRange r hr y w0 h
      · rw [he]; exact Or.inl rfl
      · rw [he]; exact hA.stRange r hr y w0 h
      · exact Or.inr (Or.inl (hVst _ _ _ hvc).1)
    · exact hA.stRange r hr y w (hoth r y w hw hc)
  · -- cmdsSome
    intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with ⟨h, he⟩ | ⟨-, he, -⟩ | ⟨h, he, -⟩ | ⟨seq, deps, st, hvc, -⟩
      · rw [he] at hs ⊢; exact hA.cmdsSome r hr y w0 h hs
      · rw [he] at hs; exact absurd rfl hs
      · rw [he] at hs ⊢; exact hA.cmdsSome r hr y w0 h hs
      · rw [(hVst _ _ _ hvc).2.2.1]; simp
    · exact hA.cmdsSome r hr y w (hoth r y w hw hc) hs
  · -- noneRec
    intro r hr y w hw hs
    have hnew : ∀ b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v) := by
      intro b st v hv
      rcases hvo r y b st v hv with h1 | ⟨hr', hy', -, seq, deps, hvc, -⟩
      · exact h1
      · exfalso; subst r; subst y; rw [R3] at hw; cases hw
        exact hpaNone (hVst _ _ _ hvc).1 hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with ⟨h, he⟩ | ⟨h0, he, -⟩ | ⟨h, he, hge, -⟩ | ⟨seq, deps, st, hvc, -⟩
      · rw [he] at hs ⊢
        obtain ⟨c1, c2⟩ := hA.noneRec r hr y w0 h hs
        exact ⟨c1, fun b st v hv => c2 b st v (hnew b st v hv)⟩
      · refine ⟨by rw [he]; simp [newInstanceDefault], fun b st v hv => hnv h0 b st v (hnew b st v hv)⟩
      · rw [he] at hs; exact absurd hs (hgeNone hge)
      · exact absurd hs (hpaNone (hVst _ _ _ hvc).1)
    · obtain ⟨c1, c2⟩ := hA.noneRec r hr y w (hoth r y w hw hc) hs
      exact ⟨c1, fun b st v hv => c2 b st v (hnew b st v hv)⟩
  · -- vbalNonneg
    intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with ⟨h, he⟩ | ⟨-, he, -⟩ | ⟨h, he, -⟩ | ⟨seq, deps, st, hvc, -⟩
      · rw [he] at hs ⊢; exact hA.vbalNonneg r hr y w0 h hs
      · rw [he] at hs; exact absurd rfl hs
      · rw [he] at hs ⊢; exact hA.vbalNonneg r hr y w0 h hs
      · rw [(hVst _ _ _ hvc).2.1]; exact hb0
    · exact hA.vbalNonneg r hr y w (hoth r y w hw hc) hs
  · -- votesLe
    intro r hr y w hw b st v hv
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hvo r y b st v hv with h1 | ⟨-, -, rfl, seq, deps, hvc, -⟩
      · rcases hX with ⟨h, he⟩ | ⟨h0, -⟩ | ⟨h, he, -⟩ | ⟨seq, deps, st', hvc, -⟩
        · rw [he]; exact hA.votesLe r hr y w0 h b st v h1
        · exact absurd h1 (hnv h0 b st v)
        · rw [he]; exact hA.votesLe r hr y w0 h b st v h1
        · rw [(hVst _ _ _ hvc).2.1]
          obtain ⟨w2, hw2, hle⟩ := hS.1.2.2.2.2.1.2 r hr y b st v h1
          rcases hro with h' | ⟨h', -⟩
          · rw [h'] at hw2; cases hw2; exact Int.le_trans hle hvc.2.2.1
          · rw [h'] at hw2; cases hw2
      · rw [(hVst _ _ _ hvc).2.1]; exact Int.le_refl _
    · rcases hvo r y b st v hv with h1 | ⟨h1, h2, -⟩
      · exact hA.votesLe r hr y w (hoth r y w hw hc) b st v h1
      · exact absurd ⟨h1, h2⟩ hc
  · -- recVote
    intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with ⟨h, he⟩ | ⟨-, he, -⟩ | ⟨h, he, -⟩ | ⟨seq, deps, st, hvc, hvE, -⟩
      · rw [he] at hs ⊢; exact hH.ev_old (hA.recVote r hr y w0 h hs)
      · rw [he] at hs
        simp [newInstanceDefault, isPA, stNONE, stPREACCEPTED, stPREACCEPTED_EQ, stACCEPTED] at hs
      · rw [he] at hs ⊢
        have := hA.recVote r hr y w0 h hs
        simpa [instVal] using hH.ev_old this
      · obtain ⟨-, e2, -, e4, e5⟩ := hVst _ _ _ hvc
        rw [e2, e4, e5]; exact hH.ev_new hvE
    · exact hH.ev_old (hA.recVote r hr y w (hoth r y w hw hc) hs)
  · -- accKeep
    have hNB := ctx_novb S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
    intro r hr y w hw b u hv hle
    have hv0 : S.ev r (.vote y b stACCEPTED u) := by
      rcases hvo r y b _ u hv with h1 | ⟨-, -, -, seq, deps, hvc, -⟩
      · exact h1
      · exfalso; rcases hvc.1 with h | h <;> exact absurd h (by decide)
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with ⟨h, he⟩ | ⟨h0, -⟩ | ⟨h, he, -⟩ | ⟨seq, deps, st, hvc, -⟩
      · rw [he] at hle ⊢; exact hA.accKeep r hr y w0 h b u hv0 hle
      · exact absurd hv0 (hnv h0 _ _ _)
      · rw [he] at hle ⊢; exact hA.accKeep r hr y w0 h b u hv0 hle
      · exfalso
        rw [(hVst _ _ _ hvc).2.1] at hle
        obtain ⟨w2, hw2, hle2⟩ := hS.1.2.2.2.2.1.2 r hr y b _ u hv0
        rcases hro with h' | ⟨h', -⟩
        · rw [h'] at hw2; cases hw2
          have hbe : b = p.ballot := zz_inj (by have := hvc.2.2.1; omega)
          subst hbe
          exact hNB seq deps st hvc _ u (Or.inr rfl) hv0
        · rw [h'] at hw2; cases hw2
    · exact hA.accKeep r hr y w (hoth r y w hw hc) b u hv0 hle
  · -- recCommit
    intro r hr y w hw hs
    obtain ⟨w1, w2, h1, h2, e1, -, -, -, -, -, hb⟩ := hview r y (Or.inr ⟨w, hw, Or.inl hs⟩)
    rw [hw] at h2; cases h2
    rw [e1] at hs
    obtain ⟨b, v, c1, c2⟩ := hA.recCommit r hr y w1 h1 hs
    exact ⟨b, v, hH.ev_old c1, Int.le_trans c2 hb⟩
  · -- commitRec
    intro r y b v hr he
    obtain ⟨w, hw, hs⟩ := hA.commitRec r y b v hr (hold r _ he (by simp [newKind]))
    obtain ⟨w1, w2, h1, h2, e1, -⟩ := hview r y (Or.inl ⟨w, hw, Or.inl hs⟩)
    rw [hw] at h1; cases h1
    exact ⟨w2, h2, by rw [e1]; exact hs⟩
  · -- fastCommitEv
    intro r y v he
    obtain ⟨h1, b, h2⟩ := hA.fastCommitEv r y v (hold r _ he (by simp [newKind]))
    exact ⟨h1, b, hH.ev_old h2⟩
  · -- makerLb
    intro r y b hr he
    obtain ⟨w, lb, hw, hlb, hle⟩ := hA.makerLb r y b hr (hold r _ he (by simp [newKind]))
    rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb, hle⟩
    · exact ⟨w, lb, h, hlb, hle⟩
  · -- lastLeBal
    intro r hr y w lb hw hlb
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rw [hlbeq] at hlb
      rcases hro with h | ⟨-, h⟩
      · exact Int.le_trans (hA.lastLeBal r hr y w0 lb h hlb) hwb
      · rw [h] at hlb; simp [newInstanceDefault] at hlb
    · exact hA.lastLeBal r hr y w lb (hoth r y w hw hc) hlb
  · -- peerOk
    intro r hr; rw [(F r).2.1]; exact hA.peerOk r hr
  · -- crtOwn
    intro r hr q hq
    exact Int.le_trans (by
      rw [(F r).2.2.2.2.1 q]
      split
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
        have := hS.2.crtMsg fr r _ x hpm (by rw [hx]; rfl)
        rw [← hpi] at *
        have h2 := hA.crtOwn r hr x.q hq
        omega
      · exact hA.crtOwn r hr q hq) (hcrtle q q)
  · -- crtRec
    intro r hr y w hw
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc
      have := hS.2.crtMsg fr r _ y hpm (by rw [hx]; rfl)
      exact Int.le_trans this (hcrtle _ _)
    · exact Int.le_trans (hA.crtRec r hr y w (hoth r y w hw hc)) (hcrtle _ _)
  · -- crtMsg
    intro fr' to m y hm' hy
    rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to m hm' with h | ⟨-, -, rp, rfl, hrp, -⟩
    · exact Int.le_trans (hA.crtMsg fr' to m y h hy) (hcrtle _ _)
    · simp only [Msg.instOf, Option.some.injEq] at hy
      obtain ⟨hx', -⟩ := ctx_rpok S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn rp hrp
      rw [← hy, hx']
      exact Int.le_trans (hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)) (hcrtle _ _)
  · -- crtEv
    intro r e y he hy
    rcases (hH.ev_iff r e).mp he with h | ⟨-, h⟩
    · obtain ⟨c1, c2⟩ := hA.crtEv r e y h hy; exact ⟨c1, Int.le_trans c2 (hcrtle _ _)⟩
    · rcases ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn e h with ⟨rp, rfl, -⟩ | ⟨seq, deps, st, -, rfl | rfl⟩
      · simp [Event.instOf] at hy
      · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hxq, Int.le_trans (hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)) (hcrtle _ _)⟩
      · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hxq, Int.le_trans (hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)) (hcrtle _ _)⟩
  · -- ownRow
    intro q hq j hj
    rw [hcq] at hj
    obtain ⟨w, lb, hw, hlb⟩ := hA.ownRow q hq j hj
    rcases R2 q _ w hw with ⟨h1, h2, h3⟩ | h
    · rw [h2, h1]; subst h3; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb⟩
    · exact ⟨w, lb, h, hlb⟩
  · -- paNoAcc
    intro r hr y w lb hw hlb hs v hv
    have hv' := hold r _ hv (by simp [newKind])
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rw [hlbeq] at hlb
      rcases hro with h | ⟨-, h⟩
      · exact hA.paNoAcc r hr y w0 lb h hlb hs v hv'
      · rw [h] at hlb; simp [newInstanceDefault] at hlb
    · exact hA.paNoAcc r hr y w lb (hoth r y w hw hc) hlb hs v hv'
  · -- paLeader
    intro r hr y w lb hw hlb hs hp hc hb
    obtain ⟨v, hv⟩ := hp
    have hv' := hold r _ hv (by simp [newKind])
    by_cases hcc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw
      have hlb' := hlb
      rw [hlbeq] at hlb
      have hmk' : ∀ w2, (S.rep r).inst y = some w2 → w2.lb = some lb →
          S.ev r (.makeBallot y lb.lastTriedBallot) :=
        fun w2 h2 h3 => (hS.1.2.2.2.2.2.2.2.2.2.2.1 r hr y w2 lb h2 h3).1
      rcases hX with ⟨h, he⟩ | ⟨h, -⟩ | ⟨h, he, -⟩ | ⟨seq, deps, st, hvc, -⟩
      · rw [he] at hc hb ⊢; exact hA.paLeader r hr y w0 lb h hlb hs ⟨v, hv'⟩ hc hb
      · rcases hro with h' | ⟨-, h'⟩
        · rw [h] at h'; cases h'
        · rw [h'] at hlb; simp [newInstanceDefault] at hlb
      · exfalso
        rw [he] at hb; simp only at hb
        have := hmk' w0 h hlb
        rw [← hb] at this
        exact hfi (maker_eq S hS.1.2.2.2.2.2.1 hxq hmk this)
      · exfalso
        rw [hvc.2.1] at hb; simp only [paRec] at hb
        rcases hro with h' | ⟨-, h'⟩
        · have := hmk' w0 h' hlb
          rw [← hb] at this
          exact hfi (maker_eq S hS.1.2.2.2.2.2.1 hxq hmk this)
        · rw [h'] at hlb; simp [newInstanceDefault] at hlb
    · exact hA.paLeader r hr y w lb (hoth r y w hw hcc) hlb hs ⟨v, hv'⟩ hc hb
  · -- prepNoProp
    intro r hr y w lb hw hlb hp
    obtain ⟨w1, hw1, hlb1⟩ : ∃ w1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb := by
      by_cases hc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
        rw [hlbeq] at hlb
        rcases hro with h | ⟨-, h⟩
        · exact ⟨w0, h, hlb⟩
        · rw [h] at hlb; simp [newInstanceDefault] at hlb
      · exact ⟨w, hoth r y w hw hc, hlb⟩
    obtain ⟨c1, c2, c3, c4, c5⟩ := hA.prepNoProp r hr y w1 lb hw1 hlb1 hp
    exact ⟨c1, fun v hv => c2 v (hold r _ hv (by simp [newKind])),
      fun v hv => c3 v (hold r _ hv (by simp [newKind])), c4, c5⟩
  · -- paMsgOnce
    intro fr' to y b; rw [hcnt0 fr' to _ (fun c => rfl)]; exact hA.paMsgOnce fr' to y b
  · -- accMsgOnce
    intro fr' to y b; rw [hcnt0 fr' to _ (fun c => rfl)]; exact hA.accMsgOnce fr' to y b
  · -- paVoteDeliv
    intro r y b st v hst hv
    rcases hvo r y b st v hv with h | ⟨hr', hy', hb', -⟩
    · rcases hA.paVoteDeliv r y b st v hst h with ⟨v0, h1⟩ | h1
      · exact Or.inl ⟨v0, hH.ev_old h1⟩
      · exact Or.inr (fun fr' => hH.allDeliv_old (h1 fr') (fun _ m hm' => hnoP _ (fun c => rfl) _ m hm'))
    · subst r; subst y; subst b; exact Or.inr hAD
  · -- parOnce
    intro a r y b h1
    rw [hH.cnt_eq] at h1 ⊢
    by_cases hnew : a = i ∧ ((snd r ++ intendedOf none r).filter (Msg.isPARat y b)).length ≠ 0
    · obtain ⟨ha, hne⟩ := hnew
      subst a
      obtain ⟨m, hmf⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hne))
      have hmf' := List.mem_filter.mp hmf
      have hmsnd : m ∈ snd r := by simpa [intendedOf] using hmf'.1
      obtain ⟨hr, rp, hmc, hrp, -⟩ := ctx_snd S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn r m hmsnd
      subst r; subst m
      obtain ⟨hx', hb', -⟩ := ctx_rpok S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn rp hrp
      simp only [Msg.isPARat, decide_eq_true_eq] at hmf'
      obtain ⟨-, hy, hbb⟩ := hmf'
      rw [hx'] at hy; subst y; rw [hb'] at hbb; subst b
      have h0 : S.cnt i fr (Msg.isPARat x p.ballot) = 0 := by
        rcases Nat.eq_zero_or_pos (S.cnt i fr (Msg.isPARat x p.ballot)) with h0 | hpos
        · exact h0
        · obtain ⟨-, hd⟩ := hA.parOnce i fr x p.ballot hpos
          exact absurd (hd n _ (msgs_of_sent S hm) (by simp [Msg.isPAat, hx])) hn
      have hsf : (snd fr ++ intendedOf none fr).filter (Msg.isPARat x p.ballot) = [.preAcceptReply rp] := by
        rcases hcase with ⟨-, -, h, -⟩ | ⟨cd, -, -, -, -, h, -⟩ | ⟨cd, seq, deps, st, -, -, -, -, -, -, -, -, h, -⟩
        · rw [h] at hmsnd; cases hmsnd
        · rw [h] at hmsnd ⊢; simp only [if_true, List.mem_singleton] at hmsnd ⊢
          simp only [Msg.preAcceptReply.injEq] at hmsnd
          subst hmsnd; simp [intendedOf, Msg.isPARat, hx', hb']
        · rw [h] at hmsnd ⊢; simp only [if_true, List.mem_singleton] at hmsnd ⊢
          simp only [Msg.preAcceptReply.injEq] at hmsnd
          subst hmsnd; simp [intendedOf, Msg.isPARat, hx', hb']
      rw [h0, hsf]
      exact ⟨by simp, hAD fr⟩
    · have hz : (if a = i then ((snd r ++ intendedOf none r).filter (Msg.isPARat y b)).length
          else 0) = 0 := by
        split
        · rename_i ha; exact Classical.byContradiction fun h => hnew ⟨ha, h⟩
        · rfl
      rw [hz, Nat.add_zero] at h1 ⊢
      obtain ⟨c1, c2⟩ := hA.parOnce a r y b h1
      exact ⟨c1, hH.allDeliv_old c2 (fun _ m hm' => hnoP _ (fun c => rfl) _ m hm')⟩
  · -- arFrom
    intro a r m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn a r _ hm' with h | ⟨-, -, rp, h, -⟩
    · obtain ⟨b', v, h1, h2⟩ := hA.arFrom a r m h; exact ⟨b', v, h1, hH.ev_old h2⟩
    · cases h
  · -- arOnce
    intro a r y b h1
    have habove : S.lastAbove r y b → S'.lastAbove r y b := by
      rintro ⟨w, lb, hw, hlb, hlt⟩
      rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
      · subst r y w; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb, hlt⟩
      · exact ⟨w, lb, h, hlb, hlt⟩
    rw [hcnt0 a r _ (fun c => rfl)] at h1 ⊢
    rcases hA.arOnce a r y b h1 with h | ⟨h2, h3⟩
    · exact Or.inl (habove h)
    · exact Or.inr ⟨h2, hH.allDeliv_old h3 (fun _ m hm' => hnoP _ (fun c => rfl) _ m hm')⟩
  · -- commitBal
    intro fr' to m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to _ hm' with h | ⟨-, -, rp, h, -⟩
    · exact hA.commitBal fr' to m h
    · cases h
  · -- sentPR
    intro r to m he
    have he0 := hold r _ he (by simp [newKind])
    obtain ⟨c1, c2, c3⟩ := hA.sentPR r to m he0
    refine ⟨fun hr => ?_, fun b st v hb => ?_, fun to' m2 hb hy => ?_⟩
    · obtain ⟨w, hw, hle⟩ := c1 hr
      rcases R2 r _ w hw with ⟨h1, h2, h3⟩ | h
      · subst r w; rw [h2]; exact ⟨w', R3, Int.le_trans hle hwb⟩
      · exact ⟨w, h, hle⟩
    · rcases (hH.evBefore_iff _ _ _ _).mp hb with h1 | ⟨-, hr, h1⟩ | ⟨hr, -, pp, pp', -, h1, -⟩
      · exact c2 b st v h1
      · subst r
        rcases ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ h1 with ⟨rp, h, -⟩ | ⟨seq, deps, st', hvc, h | h⟩
        · cases h
        · simp only [Event.vote.injEq] at h; obtain ⟨hy, hb', -, -⟩ := h
          obtain ⟨w, hw, hle⟩ := c1 hi
          rw [hy] at hw
          rcases hro with h' | ⟨h', -⟩
          · rw [h'] at hw; cases hw; rw [hb']; exact Int.le_trans hle hvc.2.2.1
          · rw [h'] at hw; cases hw
        · cases h
      · exfalso
        rcases ctx_E S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (List.mem_of_getElem? h1) with ⟨rp, h, -⟩ | ⟨s1, d1, t1, v1, h | h⟩
        · simp at h
        · cases h
        · cases h
    · have hsent : S'.ev r (.sent to' (.acceptReply m2)) := by
        obtain ⟨pp, pp', -, -, h⟩ := hb; exact List.mem_of_getElem? h
      have h0 := hold r _ hsent (by simp [newKind])
      exact c3 to' m2 (hH.evBefore_back hb h0 (fun _ => ctx_notE S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn _ (by simp [newKind]) rfl)) hy
  · -- confCover
    intro r hr e y cy he hrec c hc
    rcases (hH.ev_iff r e).mp he with h | ⟨hr', hE⟩
    · exact confLe_cover (F r).2.2.2.2.2 (hA.confCover r hr e y cy h hrec c hc)
    · subst r
      rcases hcase with ⟨-, rfl, -⟩ | ⟨cd, -, -, -, rfl, -⟩ |
        ⟨cd, seq, deps, st, σu, -, -, -, -, -, -, rfl, -, σb, hb, hc', -⟩
      · cases hE
      · simp only [List.mem_singleton] at hE; subst hE; simp [Event.recorded] at hrec
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hE
        rcases hE with rfl | rfl | rfl
        · simp [Event.recorded] at hrec
        · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
          obtain ⟨rfl, rfl⟩ := hrec
          rw [hH.rep_self, hc', hpi]
          exact uc_cov σb p.command _ p.inst p.seq c hc
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
      rcases hcase with ⟨-, -, -, -, h1, h2⟩ | ⟨-, -, -, -, -, -, -, h1, h2⟩ |
        ⟨-, -, -, -, σu, -, -, -, -, -, -, -, -, σb, -, -, -, -, h1, h2, h3, h4, h5⟩
      · exact AuxProof.clsWf_keep (hA.classWf r hr) h1 h2 hgrow
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
        rcases hcase with ⟨-, -, -, -, h1, h2⟩ | ⟨-, -, -, -, -, -, -, h1, h2⟩ |
          ⟨-, -, -, -, σu, -, -, -, -, -, -, -, -, σb, -, -, -, -, h1, h2, -, h4, h5⟩
        · exact AuxProof.clsLe_of_eq h1 h2
        · exact AuxProof.clsLe_of_eq h1 h2
        · exact AuxProof.clsLe_trans (AuxProof.clsLe_of_eq h1 h2)
            (AuxProof.clsLe_trans (ConfProof.uc_clsLe σb p.command x.q p.inst p.seq)
              (AuxProof.clsLe_of_eq h4 h5))
      · rw [hH.rep_other hr]; exact AuxProof.clsLe_refl _
    intro r hr e y cy he hrec
    rcases (hH.ev_iff r e).mp he with h | ⟨hr', hE⟩
    · exact AuxProof.clsCov_mono (hle r) (hA.classCover r hr e y cy h hrec)
    · subst r
      rcases hcase with ⟨-, rfl, -⟩ | ⟨cd, -, -, -, rfl, -⟩ |
        ⟨cd, seq, deps, st, σu, -, -, -, -, -, -, rfl, -, σb, -, -, -, -, -, -, -, h4, h5⟩
      · cases hE
      · simp only [List.mem_singleton] at hE; subst hE; simp [Event.recorded] at hrec
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hE
        rcases hE with rfl | rfl | rfl
        · simp [Event.recorded] at hrec
        · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
          obtain ⟨rfl, rfl⟩ := hrec
          rw [hH.rep_self]; intro c hc'; rw [h4, h5]
          exact ConfProof.clsCov_uc σb p.command p.inst p.seq _ hpi.symm c hc'
        · simp [Event.recorded] at hrec
  · -- paAttrs
    intro r y b st v hst hv
    rcases hvo r y b st v hv with h | ⟨hr', hy', hb', seq, deps, hvc, hv', hvE⟩
    · exact hH.ev_old (hA.paAttrs r y b st v hst h)
    · subst r; subst y; subst v
      rcases hcase with ⟨-, hE, -⟩ | ⟨cd, -, -, -, hE, -⟩ |
        ⟨cd, seq0, deps0, st0, -, -, -, -, -, -, -, hE, -⟩
      · rw [hE] at hvE; cases hvE
      · rw [hE] at hvE; simp at hvE
      · rw [hE] at hvE; simp at hvE
        exact hH.ev_new (by rw [hE]; simp [hvE])
  · -- valOk
    intro r y b v hv
    rw [hH.owner]
    exact hA.valOk r y b v (hv.imp (fun h => hold r _ h (by simp [newKind]))
      (fun h => hold r _ h (by simp [newKind])))
  · -- cmdsNe
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
    refine ⟨fun fr' to m hm' cs hc => ?_, fun r hr y w cs hw hc => ?_,
      fun r hr y w lb cs hw hlb hc => ?_, fun fr' to m hm' hs => ?_,
      fun r m he => n5 r m (hold r _ he (by simp [newKind])),
      fun r y b v hv => n6 r y b v (hv.imp (fun h => hold r _ h (by simp [newKind]))
        (fun h => hold r _ h (by simp [newKind])))⟩
    · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to m hm' with h | ⟨-, -, rp, rfl, -⟩
      · exact n1 fr' to m h cs hc
      · cases hc
    · by_cases hcc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw
        rcases hX with ⟨h, he⟩ | ⟨-, he, -⟩ | ⟨h, he, -⟩ | ⟨seq, deps, st, hvc, -⟩
        · rw [he] at hc; exact n2 r hr y w0 cs h hc
        · rw [he] at hc; simp [newInstanceDefault] at hc
        · rw [he] at hc; exact n2 r hr y w0 cs h hc
        · rw [(hVst _ _ _ hvc).2.2.1] at hc; simp only [Option.some.injEq] at hc; subst hc
          exact hcne
      · exact n2 r hr y w cs (hoth r y w hw hcc) hc
    · by_cases hcc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw
        rw [hlbeq] at hlb
        rcases hro with h | ⟨-, h⟩
        · exact n3 r hr y w0 lb cs h hlb hc
        · rw [h] at hlb; simp [newInstanceDefault] at hlb
      · exact n3 r hr y w lb cs (hoth r y w hw hcc) hlb hc
    · rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to _ hm' with h | ⟨-, -, rp, h, -⟩
      · exact n4 fr' to m h hs
      · cases h

  · -- prSent
    intro fr' to m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn fr' to _ hm' with h | ⟨-, -, rp, h, -⟩
    · exact hH.ev_old (hA.prSent fr' to m h)
    · cases h
  · -- selfOk
    intro r m he hs
    exact hA.selfOk r m (hold r _ he (by simp [newKind])) hs
  · -- selfRaw
    intro r m he
    exact hA.selfRaw r m (hold r _ he (by simp [newKind]))
  · -- pm (sixth agent)
    exact ctx_pm S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  · -- ownerCrt (p-model2)
    intro y ps h; rw [hH.owner] at h
    obtain ⟨h1, h2⟩ := hA.ownerCrt y ps h
    exact ⟨h1, Int.le_trans h2 (hcrtle _ _)⟩
  · -- execLo (p-exec)
    exact AuxProof.execLo_upd hS.2.execLo hH.rep hexe
  · -- execution fields (p-modelexec)
    refine ExecOrd.invExec_hs hS.1 hS.2.exec hH hidle (ctx_agr S S' fr i n p x w0 w' σ' E snd hS hi hfr hidle hn hm hx hH hid hpo hcrt hexe hsto hσi hro hcase hdn) hchan R4 R3
      (fun w hw hs => ?_) (fun lb' hl hne => ?_)
    · rcases hro with h | ⟨h, -⟩
      · rw [h] at hw; cases hw; exact (hcw (Or.inr (Or.inl hs))).2.1
      · rw [h] at hw; cases hw
    · rw [hlbeq] at hl
      rcases hro with h | ⟨-, h⟩
      · exact ⟨w0, lb', h, hl, hne⟩
      · subst h; simp [newInstanceDefault] at hl

end

/-- **`handlePreAccept` keeps the invariant.** -/
theorem inv_deliver_preAccept' (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : PreAccept)
    (hm : (S.sent fr i)[n]? = some (.preAccept p)) : Inv (S.deliver fr i n (.preAccept p)) := by
  have hpm := mem_msgs_of_sent S hm
  obtain ⟨hldr, -⟩ := hS.1.2.2.2.2.2.1.2.2.2.2.1 fr i p hpm
  have hc := preAccept_cases S fr i n p hidle hm hfr hldr
    (fun w h hs => hS.2.cmdsSome i hi _ w h hs)
  dsimp only at hc
  have hro := recOr_of (S.rep i) ⟨toN p.replica, toN p.inst⟩
  have hdn := deliver_delivered S fr i n (.preAccept p)
  generalize recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩ = w0 at hc hro
  obtain ⟨σ', w', E, snd, hH, hid, hpo, hcrt, hexe, hsto, hσi, hcase⟩ := hc
  have hwf := ctx_wf S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hbal := ctx_ballots S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hown := ctx_own S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hvf := ctx_vf S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  have hsafe := ctx_safe S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  obtain ⟨e1, e2, e3, e4⟩ := ctx_exec S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn
  exact ⟨⟨hwf, ctx_msgWf S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_rt S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_ntpa S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, hbal, hown, ctx_op S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, hvf, ctx_rr S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn,
    ctx_hi S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_lb S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_agr S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_dc S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, chosenSafe_of_safe _ hwf hbal hown hvf hsafe,
    ctx_dcv S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_wit S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_ac S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, e1, e2, e3, e4, ctx_slots S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_co S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, ctx_cm S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn,
    ctx_pk S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn, hsafe, ctx_reports S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn⟩, ctx_aux S _ fr i n p _ w0 w' σ' E snd hS hi hfr hidle hn hm rfl hH hid hpo hcrt hexe hsto hσi hro hcase hdn (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h))⟩

end PreAcceptProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
