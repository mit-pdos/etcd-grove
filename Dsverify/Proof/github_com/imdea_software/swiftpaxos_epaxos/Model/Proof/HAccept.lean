/-
`handleAccept` (`hAccept`): the law `inv_deliver_accept`.

Three cases (`hAccept_eq`): a stale Accept (`ballot < inst.bal`) changes nothing but the record's
creation and `crtInstance`; on a committed record an `AcceptReply` at the record's `bal` (G3,
decisions.md D5: the leader counts it); otherwise the ACCEPTED vote and its `AcceptReply`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HLocal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecHS
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.PMHS

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace AcceptProof

open HStepProof HLocal SafeProof

/-- The record `hAccept` writes on a vote. -/
def accRec (w : InstRec) (p : Accept) : InstRec :=
  { w with cmds := some p.command, deps := p.deps, seq := p.seq, bal := p.ballot,
           vbal := p.ballot, status := stACCEPTED }

theorem hAccept_eq (σ : RState) (p : Accept) :
    hAccept σ p =
      if p.ballot.slt (recOr σ ⟨toN p.replica, toN p.inst⟩).bal then
        ((bumpCrt (bumpRecvBallot σ p.ballot) (toN p.replica) p.inst).setInst
          ⟨toN p.replica, toN p.inst⟩ (recOr σ ⟨toN p.replica, toN p.inst⟩), [])
      else if stGe (recOr σ ⟨toN p.replica, toN p.inst⟩).status stCOMMITTED then
        ((bumpCrt (bumpRecvBallot σ p.ballot) (toN p.replica) p.inst).setInst
          ⟨toN p.replica, toN p.inst⟩ (recOr σ ⟨toN p.replica, toN p.inst⟩),
         [.send (toN p.leaderId) (.acceptReply
            ⟨p.replica, p.inst, (recOr σ ⟨toN p.replica, toN p.inst⟩).bal⟩)])
      else
        ((bumpCrt (bumpRecvBallot σ p.ballot) (toN p.replica) p.inst).setInst
          ⟨toN p.replica, toN p.inst⟩ (accRec (recOr σ ⟨toN p.replica, toN p.inst⟩) p),
         [.ev (.vote ⟨toN p.replica, toN p.inst⟩ p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩),
          .send (toN p.leaderId) (.acceptReply ⟨p.replica, p.inst, p.ballot⟩)]) := by
  have hr : recOr (bumpCrt (bumpRecvBallot σ p.ballot) (toN p.replica) p.inst)
      ⟨toN p.replica, toN p.inst⟩ = recOr σ ⟨toN p.replica, toN p.inst⟩ := by
    simp [recOr]
  unfold hAccept
  simp only [getOrDefault_eq, hr]
  split
  · rfl
  · split <;> simp [accRec]


/-- The three cases of `hAccept` as a handler step. -/
theorem accept_cases (S : Sys) (fr i n : Nat) (p : Accept) (hidle : S.idle i)
    (hm : (S.sent fr i)[n]? = some (.accept p)) (hfr : fr < nR)
    (hldr : p.leaderId = W32 fr)
    (hst : ∀ x w, (S.rep i).inst x = some w →
      w.status = stNONE ∨ isPA w.status ∨ w.status = stACCEPTED ∨ isCommitted w.status) :
    let x : InstId := ⟨toN p.replica, toN p.inst⟩
    let w0 := recOr (S.rep i) x
    let σ2 := bumpCrt (bumpRecvBallot (S.rep i) p.ballot) x.q p.inst
    ∃ w' E snd, HS S (S.deliver fr i n (.accept p)) i (σ2.setInst x w') E snd none ∧
      ((w' = w0 ∧ E = [] ∧ (∀ to, snd to = [])) ∨
       (w' = w0 ∧ zz w0.bal ≤ zz p.ballot ∧ isCommitted w0.status ∧
         E = [.sent fr (.acceptReply ⟨p.replica, p.inst, w0.bal⟩)] ∧
         (∀ to, snd to = if to = fr then [.acceptReply ⟨p.replica, p.inst, w0.bal⟩] else [])) ∨
       (w' = accRec w0 p ∧ zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status ∧
         E = [.vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩,
              .sent fr (.acceptReply ⟨p.replica, p.inst, p.ballot⟩)] ∧
         (∀ to, snd to = if to = fr then [.acceptReply ⟨p.replica, p.inst, p.ballot⟩] else []))) := by
  dsimp only
  have hH := hs_deliver S fr i n (.accept p) hidle hm
  simp only [hMsg] at hH
  rw [hAccept_eq] at hH
  have hro := recOr_of (S.rep i) ⟨toN p.replica, toN p.inst⟩
  generalize recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩ = w0 at hH hro ⊢
  have hl : toN p.leaderId = fr := by rw [hldr]; exact toN_W32 fr hfr
  by_cases c1 : p.ballot.slt w0.bal = true
  · simp only [c1, if_true] at hH
    exact ⟨w0, [], sendsOf [], by simpa [evsOf, pendFold] using hH,
      Or.inl ⟨rfl, rfl, fun _ => rfl⟩⟩
  · have hle : zz w0.bal ≤ zz p.ballot := by
      have := (slt_false _ _).mp (by simpa using c1); exact this
    simp only [c1, if_false, Bool.false_eq_true] at hH
    by_cases c2 : stGe w0.status stCOMMITTED = true
    · simp only [c2, if_true] at hH
      have hc : isCommitted w0.status := by
        rcases hro with h | ⟨-, h⟩
        · exact stGe_comm_of (hst _ _ h) c2
        · rw [h] at c2; simp [newInstanceDefault, stGe, stNONE, stCOMMITTED] at c2
      refine ⟨w0, _, _, hH, Or.inr (Or.inl ⟨rfl, hle, hc, ?_, fun to => ?_⟩)⟩
      · simp [evsOf, Out.hev, hl]
      · simp only [sendsOf, List.filterMap_cons, List.filterMap_nil, Out.sendTo, hl]
        by_cases h : fr = to
        · subst h; simp
        · simp [h, Ne.symm h]
    · simp only [c2, if_false, Bool.false_eq_true] at hH
      have hc : ¬ isCommitted w0.status := not_comm_of (by simpa using c2)
      refine ⟨_, _, _, hH, Or.inr (Or.inr ⟨rfl, hle, hc, ?_, fun to => ?_⟩)⟩
      · simp [evsOf, Out.hev, hl]
      · simp only [sendsOf, List.filterMap_cons, List.filterMap_nil, Out.sendTo, hl]
        by_cases h : fr = to
        · subst h; simp
        · simp [h, Ne.symm h]


/-- An accepted value `v` at `b` other than the decided value `u` is blocked at `b` (the other
orders of `b` and `u`'s choice ballot are impossible). -/
theorem blocked_of_decided (S : Sys) (hS : Inv S) (x : InstId) (b : w32) (v u : Val) (ℓ : Nat)
    (hacc : S.ev ℓ (.accept x b v)) (hcu : S.committedVal x u) (hne : u ≠ v) :
    S.blocked x b v := by
  obtain ⟨hwf, -, -, -, hbal, hown, hop, hvf, -, -, -, -, hdc, -, -, -, -, -, -, -, -, -, -, -, -,
    hsafe, hrep⟩ := hS.1
  have hxq : x.q < nR := (hS.2.crtEv ℓ _ x hacc rfl).1
  have hmk := hown.2.2.1 ℓ x b v hacc
  have hreal : realBal x b := by
    rcases (hown.1 ℓ x b hmk).1 with ⟨h1, -⟩ | ⟨h1, -⟩
    · refine Or.inl ?_
      unfold initBal
      exact eq_W32_of_zz b x.q (by omega) (by simp [nR] at hxq; omega) h1
    · exact Or.inr h1
  have hzi := zz_initBal x hxq
  have hvoter : ∀ b0, S.slowChosen x b0 u → ∃ ℓ', S.ev ℓ' (.accept x b0 u) := by
    intro b0 hsc
    obtain ⟨Q, -, hl, hQ⟩ := hsc
    obtain ⟨r, hr⟩ : ∃ r, r ∈ Q := by
      cases Q with
      | nil => simp [nR] at hl
      | cons r _ => exact ⟨r, List.mem_cons_self⟩
    exact hvf.2 r x b0 u (hQ r hr).2
  rcases hdc x u hcu with ⟨b0, hsc⟩ | ⟨hfr, hfc⟩
  · obtain ⟨hreal0, -⟩ := slowChosen_real S hbal hwf hown hvf x b0 u hsc
    rcases Int.lt_trichotomy (zz b0) (zz b) with hlt | heq | hgt
    · exact absurd ((hsafe.1 ℓ x b v hacc).1 b0 hreal0 hlt u hne)
        (fun h => not_slowChosen_of_blocked S x b0 u hsc h)
    · exfalso
      have hb : b0 = b := zz_inj heq
      subst hb
      obtain ⟨ℓ', h'⟩ := hvoter b0 hsc
      exact hne (hop.2.1 ℓ' ℓ x b0 u v h' hacc)
    · obtain ⟨ℓ', h'⟩ := hvoter b0 hsc
      exact (hsafe.1 ℓ' x b0 u h').1 b hreal hgt v (Ne.symm hne)
  · exfalso
    have hlive : S.fastLive x u := ⟨hfr, Or.inr hfc⟩
    rcases hreal with hb | hb
    · subst hb
      exact not_fastLive_of_fastBlocked S x u hxq hlive (hrep.2.2.2.2.2.2.2.1 ℓ x v hacc u)
    · exact not_fastLive_of_fastBlocked S x u hxq hlive
        ((hsafe.1 ℓ x b v hacc).2 (by simp [nR] at hxq hb; omega) u hne)

/-! ## The step's context -/

section
variable (S S' : Sys) (fr i n : Nat) (p : Accept) (x : InstId) (w0 w' : InstRec) (E : List Event)
  (snd : Nat → List Msg)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.accept p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpCrt (bumpRecvBallot (S.rep i) p.ballot) x.q p.inst).setInst x w') E snd
    none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hcase : (w' = w0 ∧ E = [] ∧ (∀ to, snd to = [])) ∨
       (w' = w0 ∧ zz w0.bal ≤ zz p.ballot ∧ isCommitted w0.status ∧
         E = [.sent fr (.acceptReply ⟨p.replica, p.inst, w0.bal⟩)] ∧
         (∀ to, snd to = if to = fr then [.acceptReply ⟨p.replica, p.inst, w0.bal⟩] else [])) ∨
       (w' = accRec w0 p ∧ zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status ∧
         E = [.vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩,
              .sent fr (.acceptReply ⟨p.replica, p.inst, p.ballot⟩)] ∧
         (∀ to, snd to = if to = fr then [.acceptReply ⟨p.replica, p.inst, p.ballot⟩] else [])))
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hcase hdn

theorem ctx_basic :
    Msg.accept p ∈ S.msgs fr i ∧ p.leaderId = W32 fr ∧
    S.ev fr (.accept x p.ballot ⟨p.command, p.seq, p.deps⟩) ∧ S.ev fr (.makeBallot x p.ballot) ∧
    x.q < nR ∧ x.i + 1 < MAX_INSTANCE ∧ 0 ≤ zz p.inst ∧ (x.i : Int) = zz p.inst ∧
    0 ≤ zz p.ballot ∧ fr ≠ i ∧ depsOk p.deps := by
  have hpm : Msg.accept p ∈ S.msgs fr i := mem_msgs_of_sent S hm
  obtain ⟨hldr, hacc⟩ := hS.1.2.2.2.2.2.1.2.2.2.2.2 fr i p hpm
  rw [← hx] at hacc
  have hmk := hS.1.2.2.2.2.2.1.2.2.1 fr x _ _ hacc
  obtain ⟨r1, r2, r3, r4⟩ := (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
  have hdeps := (hS.1.2.1 fr i _ hpm).2 p.deps (by simp [Msg.depsFields])
  refine ⟨hpm, hldr, hacc, hmk, ?_, ?_, r3, ?_, zz_nonneg_of_make S hS.1.2.2.2.2.2.1 hmk,
    (hS.1.1.2.2.2.2.2.1 fr i (List.ne_nil_of_mem hpm)).2.2, hdeps⟩
  · subst hx; simp only [toN, zz] at r1 r2 ⊢; omega
  · subst hx; exact r4
  · subst hx; exact toN_of_zz _ r3

/-- The records after the step. -/
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
    · subst h; simp only [upd_same, setInst_inst, bumpCrt_inst, bumpRB_inst, true_and]
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

/-- The new events. -/
theorem ctx_E : ∀ e ∈ E, (∃ c, e = .sent fr (.acceptReply ⟨p.replica, p.inst, c⟩)) ∨
    (e = .vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩ ∧ w' = accRec w0 p ∧
      zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status) := by
  intro e he
  rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨h1, h2, h3, rfl, -⟩
  · cases he
  · simp only [List.mem_singleton] at he; exact Or.inl ⟨_, he⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Or.inr ⟨rfl, h1, h2, h3⟩
    · exact Or.inl ⟨_, rfl⟩

/-- The new messages. -/
theorem ctx_snd : ∀ to m, m ∈ snd to → to = fr ∧
    ∃ c, m = .acceptReply ⟨p.replica, p.inst, c⟩ ∧ zz c ≤ zz p.ballot ∧ Event.sent fr m ∈ E ∧
      ((c = p.ballot ∧ w' = accRec w0 p ∧ zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status ∧
        EBefore E (.vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩) (.sent fr m)) ∨
       (c = w0.bal ∧ w' = w0 ∧ isCommitted w0.status)) := by
  intro to m hm'
  rcases hcase with ⟨-, -, h⟩ | ⟨h1, h2, h3, rfl, h⟩ | ⟨h1, h2, h3, rfl, h⟩
  · rw [h] at hm'; cases hm'
  · rw [h] at hm'; split at hm'
    · rename_i ht; simp only [List.mem_singleton] at hm'; subst hm'
      exact ⟨ht, _, rfl, h2, by simp, Or.inr ⟨rfl, h1, h3⟩⟩
    · cases hm'
  · rw [h] at hm'; split at hm'
    · rename_i ht; simp only [List.mem_singleton] at hm'; subst hm'
      exact ⟨ht, _, rfl, Int.le_refl _, by simp, Or.inl ⟨rfl, h1, h2, h3, 0, 1, by omega, rfl, rfl⟩⟩
    · cases hm'


/-- The replica fields other than the records. -/
theorem ctx_fields : ∀ r, (S'.rep r).id = (S.rep r).id ∧
    (S'.rep r).peerOrder = (S.rep r).peerOrder ∧ (S'.rep r).conflicts = (S.rep r).conflicts ∧
    (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store ∧
    (∀ q, zz ((S'.rep r).crtInstance q) =
      if r = i ∧ q = x.q then max (zz ((S.rep r).crtInstance q)) (zz p.inst)
      else zz ((S.rep r).crtInstance q)) := by
  intro r
  rw [hH.rep]
  by_cases h : r = i
  · subst h
    simp only [upd_same]
    refine ⟨by simp [RState.setInst], by simp [RState.setInst], by simp [RState.setInst],
      by simp [RState.setInst], by simp [RState.setInst], fun q => ?_⟩
    simp only [RState.setInst, true_and]
    have := zz_bumpCrt (bumpRecvBallot (S.rep r) p.ballot) x.q p.inst q
    simp only [bumpRB_crt] at this
    rw [this]; by_cases hq : q = x.q
    · subst hq; simp
    · simp [hq]
  · simp [h]

theorem ctx_crt_le : ∀ r q, zz ((S.rep r).crtInstance q) ≤ zz ((S'.rep r).crtInstance q) := by
  intro r q
  rw [(ctx_fields S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r).2.2.2.2.2 q]
  split <;> omega

theorem ctx_wf : Inv.wf S' := by
  obtain ⟨hpm, hldr, hacc, hmk, hxq, hxi, hpi0, hpi, hb0, hfi, hdeps⟩ :=
    ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have F := ctx_fields S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hS.1.1
  have hA := hS.2
  -- `w'` against `w0`
  have hw'0 : w'.id = w0.id ∧ w'.lb = w0.lb ∧ (w'.status ≠ stNONE →
      (w0.status ≠ stNONE ∧ w'.deps = w0.deps) ∨ w'.deps = p.deps) ∧
      (w'.status = stEXECUTED → w' = w0) := by
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -, h3, -⟩
    · exact ⟨rfl, rfl, fun h => Or.inl ⟨h, rfl⟩, fun _ => rfl⟩
    · exact ⟨rfl, rfl, fun h => Or.inl ⟨h, rfl⟩, fun _ => rfl⟩
    · refine ⟨rfl, rfl, fun _ => Or.inr rfl, fun h => absurd h (by simp [accRec]; decide)⟩
  have hw0 : w0.id = x ∧ (w0.status ≠ stNONE → depsOk w0.deps) ∧
      (∀ lb, w0.lb = some lb → lb.status ≠ stNONE → depsOk lb.deps) ∧
      (x.q = i → w0.lb ≠ none) ∧
      (∀ lb ps, w0.lb = some lb → lb.clientProposals = some ps → S.owner x = some ps) := by
    rcases hro with h | ⟨h, rfl⟩
    · obtain ⟨g1, -, -, g4, g5, g6, g7⟩ := w2 i hi x w0 h
      exact ⟨g1, g4, g5, g6, g7⟩
    · refine ⟨rfl, fun h' => absurd rfl h', fun lb h' => by simp [newInstanceDefault] at h',
        fun hq => ?_, fun lb ps h' => by simp [newInstanceDefault] at h'⟩
      exfalso
      have hc := hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)
      rw [← hq] at h
      obtain ⟨w, lb, hw, -⟩ := hA.ownRow x.q hxq x.i hc
      rw [show (⟨x.q, x.i⟩ : InstId) = x from rfl, h] at hw; cases hw
  have hweq : (isCommitted w0.status ∨ w0.status = stEXECUTED) → w' = w0 := by
    intro hc
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h3, -⟩
    · exact h
    · exact h
    · exact absurd (hc.elim id Or.inr) h3
  refine ⟨fun r hr => by rw [(F r).1]; exact w1 r hr, fun r hr y w hw => ?_,
    fun r hr q hq => ?_, fun r hr q k p0 hk => ?_, fun r hr q hq m' hm' => ?_,
    fun fr' to hne => ?_, fun fr' to n' hn' => ?_, fun r b hb => ?_⟩
  · rcases R1 r y w hw with ⟨rfl, rfl, rfl⟩ | h
    · obtain ⟨e1, e2, e3, -⟩ := hw'0
      obtain ⟨g1, g2, g3, g4, g5⟩ := hw0
      refine ⟨e1 ▸ g1, hxq, hxi, fun hs => ?_, fun lb hlb => g3 lb (e2 ▸ hlb), fun hq => e2 ▸ g4 hq,
        fun lb ps hlb => ?_⟩
      · rcases e3 hs with ⟨h0, h⟩ | h
        · rw [h]; exact g2 h0
        · rw [h]; exact hdeps
      · rw [hH.owner]; exact g5 lb ps (e2 ▸ hlb)
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2 r hr y w h
      exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
  · have e := (F r).2.2.2.2.2 q
    obtain ⟨c1, c2⟩ := w3 r hr q hq
    simp only [toN, zz] at e c1 c2 hxi hpi hpi0 ⊢
    rw [e]
    split
    · constructor <;> omega
    · exact ⟨c1, c2⟩
  · rw [(F r).2.2.1] at hk
    obtain ⟨k1, k2, k3⟩ := w4 r hr q k p0 hk
    refine ⟨k1, fun h => ?_, fun h => ?_⟩
    · intro hn'
      cases h' : (S.rep r).inst ⟨q, toN p0.last⟩ with
      | none => exact k2 h h'
      | some w =>
        rcases R2 r _ w h' with ⟨rfl, hy, -⟩ | h''
        · rw [hy] at hn'; rw [R3] at hn'; cases hn'
        · rw [h''] at hn'; cases hn'
    · intro hn'
      cases h' : (S.rep r).inst ⟨q, toN p0.lastWrite⟩ with
      | none => exact k3 h h'
      | some w =>
        rcases R2 r _ w h' with ⟨rfl, hy, -⟩ | h''
        · rw [hy] at hn'; rw [R3] at hn'; cases hn'
        · rw [h''] at hn'; cases hn'
  · rw [(F r).2.2.2.1] at hm'
    obtain ⟨w, hw, hs⟩ := w5 r hr q hq m' hm'
    rcases R2 r _ w hw with ⟨rfl, hy, rfl⟩ | h''
    · refine ⟨w', by rw [hy]; exact R3, ?_⟩
      rw [hweq (Or.inr hs)]; exact hs
    · exact ⟨w, h'', hs⟩
  · rw [hH.msgs] at hne
    by_cases h0 : S.msgs fr' to = []
    · rw [h0, List.nil_append] at hne
      split at hne
      · rename_i hf; rw [hf]
        simp only [intendedOf, List.append_nil] at hne
        obtain ⟨m', hm''⟩ := List.exists_mem_of_ne_nil _ hne
        obtain ⟨rfl, -⟩ := ctx_snd S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro
          hcase hdn to m' hm''
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


theorem ctx_w : zz w0.bal ≤ zz w'.bal ∧ w'.lb = w0.lb ∧ w'.id = w0.id ∧ zz w'.vbal ≤ zz w'.bal ∧
    (w' = w0 ∨ (w' = accRec w0 p ∧ zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status)) ∧
    (isCommitted w0.status ∨ w0.status = stEXECUTED → w' = w0) ∧
    (w0.status = stNONE ∨ isPA w0.status ∨ w0.status = stACCEPTED ∨ isCommitted w0.status) ∧
    zz w0.vbal ≤ zz w0.bal := by
  have h0 : (w0.status = stNONE ∨ isPA w0.status ∨ w0.status = stACCEPTED ∨
      isCommitted w0.status) ∧ zz w0.vbal ≤ zz w0.bal := by
    rcases hro with h | ⟨-, rfl⟩
    · exact ⟨hS.2.stRange i hi x w0 h, hS.1.2.2.2.2.1.1 i hi x w0 h⟩
    · exact ⟨Or.inl rfl, by simp [newInstanceDefault]⟩
  rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, h2, h3, -⟩
  · exact ⟨Int.le_refl _, rfl, rfl, h0.2, Or.inl rfl, fun _ => rfl, h0.1, h0.2⟩
  · exact ⟨Int.le_refl _, rfl, rfl, h0.2, Or.inl rfl, fun _ => rfl, h0.1, h0.2⟩
  · refine ⟨h2, rfl, rfl, Int.le_refl _, Or.inr ⟨rfl, h2, h3⟩, fun hc => ?_, h0.1, h0.2⟩
    exact absurd (hc.elim id Or.inr) h3

theorem ctx_ev : ∀ r e, S'.ev r e → S.ev r e ∨ (r = i ∧
    ((∃ c, e = .sent fr (.acceptReply ⟨p.replica, p.inst, c⟩)) ∨
     (e = .vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩ ∧ w' = accRec w0 p ∧
      zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status))) := by
  intro r e he
  rcases (hH.ev_iff r e).mp he with h | ⟨hr, h⟩
  · exact Or.inl h
  · subst r; exact Or.inr ⟨rfl, ctx_E S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn e h⟩

/-- Events of other kinds are old. -/
theorem ctx_ev_old (r : Nat) (e : Event) (he : S'.ev r e)
    (hk : ∀ c, e ≠ .sent fr (.acceptReply ⟨p.replica, p.inst, c⟩))
    (hv : e ≠ .vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩) : S.ev r e := by
  rcases ctx_ev S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r e he with h | ⟨-, ⟨c, h⟩ | ⟨h, -⟩⟩
  · exact h
  · exact absurd h (hk c)
  · exact absurd h hv

theorem ctx_notE (e : Event)
    (hk : ∀ c, e ≠ .sent fr (.acceptReply ⟨p.replica, p.inst, c⟩))
    (hv : e ≠ .vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩) : i = i → e ∉ E := by
  intro _ he
  rcases ctx_E S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn e he with ⟨c, h⟩ | ⟨h, -⟩
  · exact hk c h
  · exact hv h

theorem ctx_msgs : ∀ fr' to m, m ∈ S'.msgs fr' to → m ∈ S.msgs fr' to ∨
    (fr' = i ∧ to = fr ∧ ∃ c, m = .acceptReply ⟨p.replica, p.inst, c⟩ ∧ zz c ≤ zz p.ballot ∧
      Event.sent fr m ∈ E ∧
      ((c = p.ballot ∧ w' = accRec w0 p ∧ zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status ∧
        EBefore E (.vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩) (.sent fr m)) ∨
       (c = w0.bal ∧ w' = w0 ∧ isCommitted w0.status))) := by
  intro fr' to m hm'
  rcases hH.mem_msgs.mp hm' with h | ⟨hf, h | h⟩
  · exact Or.inl h
  · subst fr'; exact Or.inr ⟨rfl, ctx_snd S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn to m h⟩
  · simp [intendedOf] at h

theorem ctx_msgWf : Inv.msgWf S' := by
  obtain ⟨hpm, -, -, -, -, -, -, -, -, -, -⟩ := ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to m hm' with h | ⟨-, -, c, rfl, -⟩
  · exact hS.1.2.1 fr' to m h
  · refine ⟨fun q n' h => ?_, by simp [Msg.depsFields]⟩
    simp only [Msg.rawId, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl

theorem ctx_rt : Inv.replyTargets S' := by
  obtain ⟨-, -, -, hmk, -, -, -, -, -, hfi, -⟩ := ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨-, hlbeq, -⟩ := ctx_w S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  intro fr' to m y hm' hy hk
  rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to m hm' with h | ⟨-, hto, c, rfl, -⟩
  · obtain ⟨w, lb, hw, hlb⟩ := hS.1.2.2.1 fr' to m y h hy hk
    rcases R2 to y w hw with ⟨h1, h2, h3⟩ | h'
    · subst to y w; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb⟩
    · exact ⟨w, lb, h', hlb⟩
  · simp only [Msg.instOf, Option.some.injEq] at hy
    obtain ⟨w, lb, hw, hlb, -⟩ := hS.2.makerLb fr x p.ballot hfr hmk
    refine ⟨w, lb, ?_, hlb⟩
    rw [hto, R4 _ _ (Or.inl hfi), ← hy, ← hx]; exact hw

theorem ctx_ntpa : Inv.noTPA S' := by
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to m hm' with h | ⟨-, -, c, rfl, -⟩
  · exact hS.1.2.2.2.1 fr' to m h
  · exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem ctx_ballots : Inv.ballots S' := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨hwb, -, -, hvb, hw'⟩ := ctx_w S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  refine ⟨fun r hr y w hw => ?_, fun r hr y b st v he => ?_⟩
  · rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w; exact hvb
    · exact hS.1.2.2.2.2.1.1 r hr y w h
  · rcases ctx_ev S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ he with h | ⟨hr', ⟨c, h⟩ | ⟨h, h1, h2, -⟩⟩
    · obtain ⟨w, hw, hle⟩ := hS.1.2.2.2.2.1.2 r hr y b st v h
      rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h'
      · subst r y w; exact ⟨w', R3, Int.le_trans hle hwb⟩
      · exact ⟨w, h', hle⟩
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨h4, h5, -, -⟩ := h
      subst r y b; exact ⟨w', R3, by rw [h1]; exact Int.le_refl _⟩

theorem ctx_own : Inv.ballotOwner S' := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hS.1.2.2.2.2.2.1
  have hold := ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  refine ⟨fun r y b he => ?_, fun r y b v he => ?_, fun r y b v he => ?_, fun r to m hm' => ?_,
    fun r to m hm' => ?_, fun r to m hm' => ?_⟩
  · have h := hold r _ he (fun c h => by cases h) (fun h => by cases h)
    refine ⟨(o1 r y b h).1, ?_⟩
    by_cases hr : r = i
    · rw [hH.count_eq (fun _ => ctx_notE S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ (fun c h => by cases h) (fun h => by cases h) rfl)]
      exact (o1 r y b h).2
    · rw [hH.count_eq (fun h => absurd h hr)]; exact (o1 r y b h).2
  · exact hH.evBefore_old (o2 r y b v (hold r _ he (fun c h => by cases h) (fun h => by cases h)))
  · exact hH.ev_old (o3 r y b v (hold r _ he (fun c h => by cases h) (fun h => by cases h)))
  · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r to _ hm' with h | ⟨-, -, c, h, -⟩
    · obtain ⟨c1, c2⟩ := o4 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h
  · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r to _ hm' with h | ⟨-, -, c, h, -⟩
    · obtain ⟨c1, c2⟩ := o5 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h
  · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r to _ hm' with h | ⟨-, -, c, h, -⟩
    · obtain ⟨c1, c2⟩ := o6 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h

theorem ctx_op : Inv.oneProposal S' := by
  obtain ⟨p1, p2, p3⟩ := hS.1.2.2.2.2.2.2.1
  have hold := ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  refine ⟨fun r r' y b v v' he he' => ?_, fun r r' y b v v' he he' => ?_,
    fun r r' y b v v' he he' => ?_⟩
  · have h := hold r _ he (fun c h => by cases h) (fun h => by cases h)
    have h' := hold r' _ he' (fun c h => by cases h) (fun h => by cases h)
    obtain ⟨c1, c2, c3⟩ := p1 r r' y b v v' h h'
    refine ⟨c1, c2, ?_⟩
    by_cases hr : r = i
    · rw [hH.count_eq (fun _ => ctx_notE S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ (fun c h => by cases h) (fun h => by cases h) rfl)]
      exact c3
    · rw [hH.count_eq (fun h => absurd h hr)]; exact c3
  · exact p2 r r' y b v v' (hold r _ he (fun c h => by cases h) (fun h => by cases h))
      (hold r' _ he' (fun c h => by cases h) (fun h => by cases h))
  · exact p3 r r' y b v v' (hold r _ he (fun c h => by cases h) (fun h => by cases h))
      (hold r' _ he' (fun c h => by cases h) (fun h => by cases h))

theorem ctx_vf : Inv.votesFollowProposals S' := by
  obtain ⟨-, -, hacc, -⟩ := ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨v1, v2⟩ := hS.1.2.2.2.2.2.2.2.1
  refine ⟨fun r y b st v he hst => ?_, fun r y b v he => ?_⟩
  · rcases ctx_ev S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ he with h | ⟨-, ⟨c, h⟩ | ⟨h, -⟩⟩
    · obtain ⟨l, v0, h1, h2⟩ := v1 r y b st v h hst; exact ⟨l, v0, hH.ev_old h1, h2⟩
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨-, -, rfl, -⟩ := h; exact absurd hst acc_not_pa
  · rcases ctx_ev S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ he with h | ⟨-, ⟨c, h⟩ | ⟨h, -⟩⟩
    · obtain ⟨l, h1⟩ := v2 r y b v h; exact ⟨l, hH.ev_old h1⟩
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨h4, h5, -, h6⟩ := h
      subst y b v; exact ⟨fr, hH.ev_old hacc⟩


theorem ctx_cv : ∀ y v, S'.committedVal y v ↔ S.committedVal y v := by
  intro y v
  constructor
  · rintro (⟨r, b, h⟩ | ⟨fr', to, m, hm', hy, rfl⟩)
    · exact Or.inl ⟨r, b, ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ h (fun c h => by cases h) (fun h => by cases h)⟩
    · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to _ hm' with h | ⟨-, -, c, h, -⟩
      · exact Or.inr ⟨fr', to, m, h, hy, rfl⟩
      · cases h
  · rintro (⟨r, b, h⟩ | ⟨fr', to, m, hm', hy, rfl⟩)
    · exact Or.inl ⟨r, b, hH.ev_old h⟩
    · exact Or.inr ⟨fr', to, m, hH.msgs_old hm', hy, rfl⟩

theorem ctx_prep : ∀ r m e, S'.prepReport r m e → S.prepReport r m e ∧ (r = i → e ∉ E) := by
  rintro r m e ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
  · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r to _ hm' with h | ⟨-, -, c, h, -⟩
    · have hn' : r = i → Event.sent to (.prepareReply m) ∉ E :=
        fun _ => ctx_notE S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ (fun c h => by cases h) (fun h => by cases h) rfl
      exact ⟨⟨ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ he (fun c h => by cases h) (fun h => by cases h),
        Or.inl ⟨to, h, rfl⟩⟩, hn'⟩
    · cases h
  · exact ⟨⟨ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ he (fun c h => by cases h) (fun h => by cases h), Or.inr rfl⟩,
      fun _ => ctx_notE S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ (fun c h => by cases h) (fun h => by cases h) rfl⟩

/-- Every report of `i` about `x` (in `S`) is at a ballot at most `w0.bal`. -/
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

theorem ctx_sentE : ∀ to m, Event.sent to m ∈ E → to = fr ∧
    ∃ c, m = .acceptReply ⟨p.replica, p.inst, c⟩ ∧ zz w0.bal ≤ zz c := by
  intro to m h
  rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨-, h2, -, rfl, -⟩
  · cases h
  · simp only [List.mem_singleton, Event.sent.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, Int.le_refl _⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · cases h
    · simp only [Event.sent.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, h2⟩

theorem ctx_rr : Inv.repliesReportVotes S' := by
  obtain ⟨q1, q2, q3⟩ := hS.1.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, hxq, -⟩ := ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨hwb, -⟩ := ctx_w S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  refine ⟨fun r m e hp => ?_, fun a r m hm' => ?_, fun a r m hm' => ?_⟩
  · obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r m e hp
    obtain ⟨c1, c2, c3, c4, c5⟩ := q1 r m e hp0
    refine ⟨c1, fun hs => hH.evBefore_old (c2 hs), fun hs => (hcv _ _).mpr (c3 hs),
      fun hs b st v hb => c4 hs b st v (hH.evBefore_back hb hp0.1 hne), fun b st v hb => ?_⟩
    rcases (hH.evBefore_iff _ _ _ _).mp hb with h | ⟨-, hr, h⟩ | ⟨hr, -, pp, pp', -, h, -⟩
    · exact c5 b st v h
    · subst r
      rcases ctx_E S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ h with ⟨c, h⟩ | ⟨h, -, h2, -⟩
      · cases h
      · simp only [Event.vote.injEq] at h; obtain ⟨hy, hb', -, -⟩ := h
        rw [hb']
        exact Int.le_trans (ctx_repBal S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn m e hp0 hy) h2
    · exact absurd (List.mem_of_getElem? h) (hne hr)
  · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn a r _ hm' with h | ⟨-, -, c, h, -⟩
    · obtain ⟨c1, c2, c3, c4⟩ := q2 a r m h
      refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
      · obtain ⟨v, hv⟩ := c1; exact ⟨v, hH.ev_old hv⟩
      · obtain ⟨d1, v, d2, d3⟩ := c2 hs; exact ⟨d1, v, hH.ev_old d2, d3⟩
      · obtain ⟨v, d2, d3⟩ := c3 hs; exact ⟨v, hH.ev_old d2, d3⟩
      · obtain ⟨v, d2, d3⟩ := c4 hs; exact ⟨v, (hcv _ _).mpr d2, d3⟩
    · cases h
  · -- the reports of `a` before an AcceptReply's send, when the send is new
    have key : ∀ (m' : PrepareReply) (e' : Event) (c : w32), S'.prepReport a m' e' →
        (Msg.prepareReply m').instOf = some x → a = i → zz w0.bal ≤ zz c →
        zz m'.ballot ≤ zz c := by
      intro m' e' c hp hy ha hc
      subst a
      obtain ⟨hp0, -⟩ := ctx_prep S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn i m' e' hp
      simp only [Msg.instOf, Option.some.injEq] at hy
      exact Int.le_trans (ctx_repBal S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn m' e' hp0 hy) hc
    rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn a r _ hm' with h | ⟨ha, hr, c, hmc, hcb, hsE, hcs⟩
    · rcases q3 a r m h with ⟨v, hv⟩ | ⟨⟨b, v, hv⟩, c2⟩
      · exact Or.inl ⟨v, hH.evBefore_old hv⟩
      · refine Or.inr ⟨⟨b, v, hH.evBefore_old hv⟩, fun m' e' hp hy hb => ?_⟩
        obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn a m' e' hp
        rcases (hH.evBefore_iff _ _ _ _).mp hb with h1 | ⟨-, ha, h1⟩ | ⟨ha, -, pp, pp', -, h1, -⟩
        · exact c2 m' e' hp0 hy h1
        · obtain ⟨-, c, hmc, hc⟩ := ctx_sentE S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ _ h1
          simp only [Msg.acceptReply.injEq] at hmc; subst hmc
          refine key m' e' c hp ?_ ha hc
          rw [hy, hx]
        · exact absurd (List.mem_of_getElem? h1) (hne ha)
    · simp only [Msg.acceptReply.injEq] at hmc; subst hmc a
      rcases hcs with ⟨rfl, -, -, -, hEB⟩ | ⟨rfl, hw', hc⟩
      · refine Or.inl ⟨⟨p.command, p.seq, p.deps⟩,
          (hH.evBefore_iff _ _ _ _).mpr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))⟩
        rw [hr]; simp only; rw [← hx]; exact hEB
      · have hw0 : (S.rep i).inst x = some w0 := by
          rcases hro with h | ⟨-, rfl⟩
          · exact h
          · exact absurd hc none_not_comm
        obtain ⟨b, v, hv, -⟩ := hS.2.recCommit i hi x w0 hw0 hc
        refine Or.inr ⟨⟨b, v, ?_⟩, fun m' e' hp hy hb => key m' e' _ hp ?_ rfl (Int.le_refl _)⟩
        · rw [← hx]
          exact (hH.evBefore_iff _ _ _ _).mpr (Or.inr (Or.inl ⟨hv, rfl, by rw [hr]; exact hsE⟩))
        · rw [hy, hx]


theorem ctx_hi : Inv.prepReplyHighest S' := by
  intro r m e hp b st v hb
  obtain ⟨hp0, hne⟩ := ctx_prep S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r m e hp
  exact hS.1.2.2.2.2.2.2.2.2.2.1 r m e hp0 b st v (hH.evBefore_back hb hp0.1 hne)

theorem ctx_lb : Inv.lbInv S' := by
  obtain ⟨-, -, -, hmk, hxq, -, -, -, -, hfi, -⟩ := ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨-, hlbeq, -, -, hw'⟩ := ctx_w S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hold := ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  intro r hr y w lb hw hlb
  -- the old record and its facts
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
    · exact Or.inl (hold r _ hv (fun c h => by cases h) (fun h => by cases h))
    · exact Or.inr (hold r _ hv (fun c h => by cases h) (fun h => by cases h))
  · obtain ⟨d1, d2, v, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, v, hH.ev_old d3, d4⟩
  · intro a m' h; obtain ⟨b1, b2, b3, b4⟩ := q3 a m' h; exact ⟨b1, b2, hH.deliveredMsg_old b3, b4⟩
  · intro a h; obtain ⟨b1, b2, m', b3, b4⟩ := q3' a h
    exact ⟨b1, b2, m', hH.deliveredMsg_old b3, b4⟩
  · rcases hrel with ⟨rfl, -⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
    · rcases hw' with rfl | ⟨rfl, -, -⟩
      · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
      · -- the Accept's ballot is `fr`'s, `lastTriedBallot` the replica's own: they differ
        exfalso
        simp only [accRec] at c3
        rw [← c3] at a1
        exact hfi (maker_eq S hS.1.2.2.2.2.2.1 hxq hmk a1)
  · obtain ⟨c1, c2⟩ := a9 hp
    refine ⟨c1, fun e he => ?_⟩
    obtain ⟨d1, d2, d3⟩ := c2 e he
    refine ⟨d1, d2, ?_⟩
    rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, hH.deliveredMsg_old e2⟩
    · exact Or.inr ⟨e1, hH.ev_old e2⟩

theorem ctx_agr : Inv.agreement S' := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨-, -, -, -, hw', hweq, -⟩ := ctx_w S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  refine ⟨fun y v v' h h' => hS.1.2.2.2.2.2.2.2.2.2.2.2.1.1 y v v' ((hcv _ _).mp h)
    ((hcv _ _).mp h'), fun r hr y w hw hc => ?_⟩
  rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
  · subst r y w
    rcases hw' with he | ⟨he, -, -⟩
    · rw [he] at hc ⊢
      rcases hro with h | ⟨-, h0⟩
      · obtain ⟨c1, c2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 i hr x w0 h hc
        exact ⟨c1, (hcv _ _).mpr c2⟩
      · rw [h0] at hc; exact absurd hc none_not_comm
    · rw [he] at hc; exact absurd hc acc_not_comm
  · obtain ⟨c1, c2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 r hr y w h hc
    exact ⟨c1, (hcv _ _).mpr c2⟩

theorem ctx_dc : Inv.decidedChosen S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  intro y v hv
  rcases hS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 y v ((hcv _ _).mp hv) with ⟨b, Q, h1, h2, h3⟩ | ⟨⟨Q, h1, h2, h3⟩, hf⟩
  · exact Or.inl ⟨b, Q, h1, h2, fun r hr => ⟨(h3 r hr).1, hH.ev_old (h3 r hr).2⟩⟩
  · refine Or.inr ⟨⟨Q, h1, h2, fun r hr => ?_⟩, hH.ev_old hf⟩
    obtain ⟨c1, c2, st, c3, c4⟩ := h3 r hr
    exact ⟨c1, c2, st, c3, hH.ev_old c4⟩

theorem ctx_dcv : Inv.depsCover S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  intro y z vy vz hyz hy hz hi'
  exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y z vy vz hyz ((hcv _ _).mp hy) ((hcv _ _).mp hz) hi'

theorem ctx_wit : Inv.witnesses S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  intro y v hv hn'
  obtain ⟨W, w1, w2, w3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y v ((hcv _ _).mp hv) hn'
  exact ⟨W, w1, w2, fun r hr => by
    obtain ⟨c1, d, c2, c3⟩ := w3 r hr; exact ⟨c1, d, hH.ev_old c2, c3⟩⟩

theorem ctx_ac : Inv.attrsCover S' := by
  intro r e y cy z cz d hrec hyz hb hint
  have h2 := ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ (by obtain ⟨p1, p2, -, -, h⟩ := hb; exact List.mem_of_getElem? h)
    (fun c h => by cases h) (fun h => by cases h)
  exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r e y cy z cz d hrec hyz
    (hH.evBefore_back hb h2 (fun _ => ctx_notE S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ (fun c h => by cases h) (fun h => by cases h) rfl))
    hint


/-- An executed or committed record is unchanged. -/
theorem ctx_inst_comm : ∀ r y, ((∃ w, (S.rep r).inst y = some w ∧
      (isCommitted w.status ∨ w.status = stEXECUTED)) ∨
    (∃ w, (S'.rep r).inst y = some w ∧ (isCommitted w.status ∨ w.status = stEXECUTED))) →
    (S'.rep r).inst y = (S.rep r).inst y := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨-, -, -, -, hw', hweq, -⟩ := ctx_w S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  intro r y h
  by_cases hc : r = i ∧ y = x
  · obtain ⟨rfl, rfl⟩ := hc
    rw [R3]
    rcases h with ⟨w, hw, hs⟩ | ⟨w, hw, hs⟩
    · rcases hro with h' | ⟨h', -⟩
      · rw [h'] at hw ⊢; cases hw; rw [hweq hs]
      · rw [h'] at hw; cases hw
    · rw [R3] at hw; cases hw
      rcases hw' with he | ⟨he, -, -⟩
      · rcases hro with h' | ⟨-, h0⟩
        · rw [h', he]
        · exfalso; rw [he, h0] at hs
          rcases hs with hs | hs
          · exact none_not_comm hs
          · simp [newInstanceDefault, stNONE, stEXECUTED] at hs
      · exfalso; rw [he] at hs; simp only [accRec] at hs
        rcases hs with hs | hs
        · exact acc_not_comm hs
        · exact absurd hs (by decide)
  · exact R4 r y (by
      by_cases h1 : r = i
      · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
      · exact Or.inl h1)

theorem ctx_executed : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
  intro r y
  constructor
  · rintro ⟨w, hw, hs⟩
    have := ctx_inst_comm S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r y (Or.inr ⟨w, hw, Or.inr hs⟩)
    exact ⟨w, by rw [← this]; exact hw, hs⟩
  · rintro ⟨w, hw, hs⟩
    have := ctx_inst_comm S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r y (Or.inl ⟨w, hw, Or.inr hs⟩)
    exact ⟨w, by rw [this]; exact hw, hs⟩

theorem ctx_dEdge : S'.dEdge = S.dEdge := by
  funext y z; simp only [Sys.dEdge, ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn]

theorem ctx_sccOrd : S'.sccOrd = S.sccOrd := by
  funext y z; simp only [Sys.sccOrd, ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn]

theorem ctx_exec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧ Inv.execPrefix S' := by
  have hex := ctx_executed S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr
    refine ⟨by rw [hH.execLog]; exact e1, fun y => by rw [hH.execLog, hex]; exact e2 y,
      fun y w hw hs => ?_⟩
    have he := ctx_inst_comm S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r y (Or.inr ⟨w, hw, Or.inr hs⟩)
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
  · intro r hr i0 j y z hij hy hz ht
    rw [hH.execLog] at hy hz; rw [ctx_dEdge S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn, ctx_sccOrd S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn] at *
    exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr i0 j y z hij hy hz ht
  · have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
      intro r k
      by_cases hri : r = i
      · subst r
        have hc0 : S.execCur i = [] := hidle.2
        simp only [Sys.lexec, Sys.curSlots, hH.execCur, hc0, hH.execLog, List.append_nil]
        refine slotsOn_congr _ _ _ k (fun y hy => ?_)
        have hey : (S.rep i).executed y := ((hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi).2.1 y).mp hy
        obtain ⟨w, hw, hs⟩ := hey
        rw [ctx_inst_comm S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn i y (Or.inl ⟨w, hw, Or.inr hs⟩)]
      · simp only [Sys.lexec, Sys.curSlots, hH.execCur, hH.execLog, hH.execIdx, hH.rep_other hri]
    obtain ⟨p1, p2, p3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
    · rw [hlx, hH.gexec]; exact p1 r hr k
    · rw [hlx]
      have : (S'.rep r).store = (S.rep r).store :=
        (ctx_fields S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r).2.2.2.2.1
      rw [this]; exact p2 r hr k
    · rw [hlx] at h; rw [hH.gexec]; exact p3 r hr k pre e post h

theorem ctx_slots : Inv.slots S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨s1, s2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun y v hv => ?_, fun y ps h => ?_⟩
  · rw [hH.owner]; exact s1 y v ((hcv _ _).mp hv)
  · rw [hH.owner] at h; rw [hH.ops]; exact s2 y ps h

theorem ctx_co : Inv.clientOps S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hso : S'.slotOp = S.slotOp := by funext sl; simp only [Sys.slotOp, hH.owner]
  have := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [Inv.clientOps, hso, hH.gexec, hH.fired, hH.ops, hcv] at this ⊢
  exact this

theorem ctx_cm : Inv.commitMsgs S' := by
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to _ hm' with h | ⟨-, -, c, h, -⟩
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
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨hwb, -, -, -, hw', -⟩ := ctx_w S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  refine ⟨fun r y w hw => ?_, fun r e he => hH.ev_old he, fun r y b st v he => ?_,
    fun y v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ _ he (fun c h => by cases h) (fun h => by cases h)),
    fun a y m hm' _ _ => ?_⟩
  · rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w
      refine ⟨w', R3, hwb, fun hs => Or.inl ?_⟩
      rcases hw' with he | ⟨he, -, -⟩
      · rw [he]; exact hs
      · rw [he]; simp only [accRec]; decide
    · exact ⟨w, h, Int.le_refl _, fun hs => Or.inl hs⟩
  · rcases ctx_ev S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ he with h | ⟨hr, ⟨c, h⟩ | ⟨h, -, h2, -⟩⟩
    · exact Or.inl h
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨hy, hb, hst, hv⟩ := h
      subst r y b st v
      refine Or.inr ⟨fun w hw => ?_, fun h => absurd h acc_not_pa, fun h => absurd h acc_not_pa⟩
      rcases hro with h' | ⟨h', -⟩
      · rw [h'] at hw; cases hw; exact ⟨h2, fun h => absurd h acc_not_pa⟩
      · rw [h'] at hw; cases hw
  · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn y.q a _ hm' with h | ⟨-, -, c, h, -⟩
    · exact Or.inl h
    · cases h

theorem ctx_safe : Inv.safe S' :=
  safe_step (ctx_mono S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn) hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun r y b v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ he (fun c h => by cases h) (fun h => by cases h)))
    (fun r y b v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ he (fun c h => by cases h) (fun h => by cases h)))

theorem ctx_reports : Inv.reports S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrepo⟩ :=
    hS.1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hrepo
  have hmo := ctx_mono S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hP := ctx_prep S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  refine ⟨fun r m e hp => c1 r m e (hP r m e hp).1, fun r m e hp => c2 r m e (hP r m e hp).1,
    fun r m e hp => c3 r m e (hP r m e hp).1, fun r m e hp b u hb => ?_, fun r m e hr hp => ?_,
    fun r y b st st' v v' h1 h2 h3 h4 => ?_, fun y v m e h1 h2 h3 => ?_,
    fun r y v h1 w => ?_, fun r m e hp => c9 r m e (hP r m e hp).1⟩
  · obtain ⟨hp0, hne⟩ := hP r m e hp
    exact c4 r m e hp0 b u (hH.evBefore_back hb hp0.1 hne)
  · obtain ⟨w, hw, hle⟩ := c5 r m e hr (hP r m e hp).1
    obtain ⟨w', hw', hle', -⟩ := hmo.bal r _ w hw
    exact ⟨w', hw', Int.le_trans hle hle'⟩
  · refine c6 r y b st st' v v' h1 h2 ?_ ?_
    · exact ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ h3 (fun c h => by cases h) (fun h => by
        simp only [Event.vote.injEq] at h; obtain ⟨-, -, rfl, -⟩ := h; exact acc_not_pa h1)
    · exact ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ h4 (fun c h => by cases h) (fun h => by
        simp only [Event.vote.injEq] at h; obtain ⟨-, -, rfl, -⟩ := h; exact acc_not_pa h2)
  · exact c7 y v m e (ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ _ h1 (fun c h => by cases h) (fun h => by cases h))
      (hP _ m e h2).1 h3
  · exact fastBlocked_mono hmo
      (c8 r y v (ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r _ h1 (fun c h => by cases h) (fun h => by cases h)) w)


theorem ctx_crt_eq : ∀ q, zz ((S'.rep q).crtInstance q) = zz ((S.rep q).crtInstance q) := by
  obtain ⟨hpm, -, -, -, hxq, -, -, hpi, -⟩ := ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  intro q
  rw [(ctx_fields S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn q).2.2.2.2.2 q]
  split
  · rename_i hc; obtain ⟨rfl, hq⟩ := hc
    have := hS.2.crtMsg fr q _ x hpm (by rw [hx]; rfl)
    rw [← hq] at this; rw [← hpi] at *; omega
  · rfl


/-- No old vote of `i` for `x` when it had no record. -/
theorem ctx_novote (h : (S.rep i).inst x = none) : ∀ b st v, ¬ S.ev i (.vote x b st v) := by
  intro b st v hv
  obtain ⟨w, hw, -⟩ := hS.1.2.2.2.2.1.2 i hi x b st v hv
  rw [h] at hw; cases hw

/-- (`InvPM.arOk`, G3) after the step. -/
theorem ctx_arOk : ∀ a r (m : AcceptReply), Msg.acceptReply m ∈ S'.msgs a r → ∀ v,
    S'.ev r (.accept (arX m) m.ballot v) →
    S'.ev a (.vote (arX m) m.ballot stACCEPTED v) ∨ S'.committedVal (arX m) v ∨
    (∃ w, (S'.rep r).inst (arX m) = some w ∧ zz m.ballot < zz w.bal) ∨
    ∃ M : List Nat, M.Nodup ∧ nR / 2 + 1 ≤ M.length ∧ a ∉ M ∧ ∀ q ∈ M, q < nR ∧
      ¬ S'.ev q (.vote (arX m) m.ballot stACCEPTED v) ∧
      (∃ wq, (S'.rep q).inst (arX m) = some wq ∧ zz m.ballot < zz wq.bal) ∧
      ∀ m' : AcceptReply, Msg.acceptReply m' ∈ S'.msgs q r → arX m' = arX m →
        m'.ballot ≠ m.ballot := by
  obtain ⟨-, -, hacc, hmk, -, -, -, -, -, hfi, -⟩ := ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨-, -, -, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hold := ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hmo := ctx_mono S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hA := hS.2
  have hvo : ∀ q y b v, S'.ev q (.vote y b stACCEPTED v) → S.ev q (.vote y b stACCEPTED v) ∨
      (q = i ∧ y = x ∧ b = p.ballot ∧ zz w0.bal ≤ zz p.ballot) := by
    intro q y b v he
    rcases ctx_ev S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn q _ he with h | ⟨hq, ⟨c, h⟩ | ⟨h, -, h2, -⟩⟩
    · exact Or.inl h
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨rfl, rfl, -, -⟩ := h
      exact Or.inr ⟨hq, rfl, rfl, h2⟩
  have hiw : ∀ wq, (S.rep i).inst x = some wq → wq = w0 := by
    intro wq h; rcases hro with h' | ⟨h', -⟩
    · rw [h] at h'; exact Option.some.inj h'
    · rw [h] at h'; cases h'
  intro a r m hm' v hv
  have hv0 : S.ev r (.accept (arX m) m.ballot v) :=
    hold r _ hv (fun c h => by cases h) (fun h => by cases h)
  rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn a r _ hm' with hmo' | ⟨ha, hr, c, hmc, hcb, hsE, hcs⟩
  · -- an old reply
    rcases hA.pm.arOk a r m hmo' v hv0 with h | h | ⟨w, hw, hlt⟩ | ⟨M, hM, hl, ha, hMm⟩
    · exact Or.inl (hH.ev_old h)
    · exact Or.inr (Or.inl ((hcv _ _).mpr h))
    · obtain ⟨w2, hw2, hle, -⟩ := hmo.bal r _ w hw
      exact Or.inr (Or.inr (Or.inl ⟨w2, hw2, Int.lt_of_lt_of_le hlt hle⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨M, hM, hl, ha, fun q hq => ?_⟩))
      obtain ⟨h1, h2, ⟨wq, hwq, hlt⟩, h4⟩ := hMm q hq
      obtain ⟨wq2, hwq2, hle, -⟩ := hmo.bal q _ wq hwq
      refine ⟨h1, fun hv' => ?_, ⟨wq2, hwq2, Int.lt_of_lt_of_le hlt hle⟩, fun m'' hm'' hx'' => ?_⟩
      · rcases hvo _ _ _ _ hv' with h | ⟨hqi, hy, hb, hle'⟩
        · exact h2 h
        · rw [hqi, hy] at hwq; rw [hiw wq hwq, hb] at hlt; omega
      · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn q r _ hm'' with h | ⟨hq', -, c', hmc', -, hsE', -⟩
        · exact h4 m'' h hx''
        · rw [hq'] at hwq
          obtain ⟨-, c'', hmc'', hc''⟩ := ctx_sentE S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ _ hsE'
          rw [hmc'] at hmc''
          simp only [Msg.acceptReply.injEq, AcceptReply.mk.injEq, true_and] at hmc' hmc''
          subst hmc' hmc''
          have hw2 : (S.rep i).inst x = some wq := by rw [hx]; rw [← hx''] at hwq; exact hwq
          rw [hiw wq hw2] at hlt
          intro he
          have he' : c' = m.ballot := he
          rw [← he'] at hlt; omega
  · -- the new reply, of `i` to `fr`
    rw [ha, hr]; rw [hr] at hv0
    simp only [Msg.acceptReply.injEq] at hmc
    have hmx : arX m = x := by rw [hmc, hx]
    have hmb : m.ballot = c := by rw [hmc]
    rw [hmx, hmb] at hv0 ⊢
    rcases hcs with ⟨rfl, -, -, -, hEB⟩ | ⟨rfl, -, hc⟩
    · -- the vote: `v` is the Accept's value
      have hve : v = ⟨p.command, p.seq, p.deps⟩ := hS.1.2.2.2.2.2.2.1.2.1 fr fr x _ v _ hv0 hacc
      subst hve
      obtain ⟨p1, p2, -, h1, -⟩ := hEB
      exact Or.inl (hH.ev_new (List.mem_of_getElem? h1))
    · -- a committed acceptor: its reply is at its `bal`
      have hw0 : (S.rep i).inst x = some w0 := by
        rcases hro with h | ⟨-, rfl⟩
        · exact h
        · exact absurd hc none_not_comm
      obtain ⟨wf, lbf, hwf, hlbf, hlef⟩ := hA.makerLb fr x p.ballot hfr hmk
      have hlbal := hA.lastLeBal fr hfr x wf lbf hwf hlbf
      have hwf' : (S'.rep fr).inst x = some wf := by rw [R4 fr x (Or.inl hfi)]; exact hwf
      by_cases hlt : zz w0.bal < zz wf.bal
      · exact Or.inr (Or.inr (Or.inl ⟨wf, hwf', hlt⟩))
      have hcb' : w0.bal = p.ballot := zz_inj (by omega)
      rw [hcb'] at hv0 ⊢
      have hve : v = ⟨p.command, p.seq, p.deps⟩ := hS.1.2.2.2.2.2.2.1.2.1 fr fr x _ v _ hv0 hacc
      subst hve
      obtain ⟨-, hcu⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 i hi x w0 hw0 hc
      by_cases hu : instVal w0 = ⟨p.command, p.seq, p.deps⟩
      · exact Or.inr (Or.inl ((hcv _ _).mpr (hu ▸ hcu)))
      obtain ⟨M, hM, hl, hMm⟩ := blocked_of_decided S hS x p.ballot _ _ fr hacc hcu hu
      have hiM : i ∉ M := by
        intro h
        obtain ⟨-, -, wa, hwa, hlt'⟩ := hMm i h
        rw [hw0] at hwa; cases hwa; rw [hcb'] at hlt'; omega
      refine Or.inr (Or.inr (Or.inr ⟨M, hM, hl, hiM, fun q hq => ?_⟩))
      have hqi : q ≠ i := fun h => hiM (h ▸ hq)
      obtain ⟨hqn, hnv, wq, hwq, hltq⟩ := hMm q hq
      refine ⟨hqn, fun hv' => ?_, ⟨wq, by rw [R4 q x (Or.inl hqi)]; exact hwq, hltq⟩,
        fun m'' hm'' hx'' hb'' => ?_⟩
      · rcases hvo _ _ _ _ hv' with h | ⟨h, -⟩
        · exact hnv h
        · exact hqi h
      · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn q fr _ hm'' with h | ⟨hq', -⟩
        · have hacc'' : S.ev fr (.accept (arX m'') m''.ballot ⟨p.command, p.seq, p.deps⟩) := by
            rw [hx'', hb'']; exact hacc
          rcases hA.pm.arOk q fr m'' h _ hacc'' with h1 | h1 | ⟨w3, hw3, hlt3⟩ |
            ⟨Mq, hMq, hlq, hqMq, hMqm⟩
          · rw [hx'', hb''] at h1; exact hnv h1
          · rw [hx''] at h1
            exact hu (hS.1.2.2.2.2.2.2.2.2.2.2.2.1.1 x _ _ hcu h1)
          · rw [hx'', hwf] at hw3; cases hw3; rw [hb''] at hlt3; omega
          · have hqfr : q ≠ fr := (hS.1.1.2.2.2.2.2.1 q fr (List.ne_nil_of_mem h)).2.2
            have hnd : [q, i, fr].Nodup := by
              simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
                List.nodup_nil, and_true]
              refine ⟨fun h => h.elim hqi hqfr, ?_⟩
              simpa using Ne.symm hfi
            obtain ⟨a', ha1, ha2⟩ := meet (U := List.range nR) hMq hnd
              (fun a h => List.mem_range.mpr (hMqm a h).1)
              (by
                intro a h
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with h | h | h <;> rw [h] <;> exact List.mem_range.mpr ‹_›)
              (by simp [nR] at hlq ⊢; omega)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha2
            rcases ha2 with h2 | h2 | h2 <;> rw [h2] at ha1
            · exact hqMq ha1
            · obtain ⟨-, -, ⟨w4, hw4, hlt4⟩, -⟩ := hMqm _ ha1
              rw [hx'', hw0] at hw4; cases hw4; rw [hb''] at hlt4; omega
            · obtain ⟨-, -, ⟨w4, hw4, hlt4⟩, -⟩ := hMqm _ ha1
              rw [hx'', hwf] at hw4; cases hw4; rw [hb''] at hlt4; omega
        · exact hqi hq'

theorem ctx_aux (hchan : S'.proposeChan = S.proposeChan) : InvAux S' := by
  obtain ⟨hpm, hldr, hacc, hmk, hxq, hxi, hpi0, hpi, hb0, hfi, hdeps⟩ := ctx_basic S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  obtain ⟨hwb, hlbeq, hid, hvb, hw', hweq, hrange0, hvb0⟩ := ctx_w S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hA := hS.2
  have hold := ctx_ev_old S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hev := ctx_ev S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have F := ctx_fields S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hcrt := ctx_crt_le S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hcq := ctx_crt_eq S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  have hnv := ctx_novote S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
  -- the vote record
  have hacR : (accRec w0 p).status = stACCEPTED ∧ (accRec w0 p).vbal = p.ballot ∧
      (accRec w0 p).bal = p.ballot ∧ (accRec w0 p).cmds = some p.command ∧
      instVal (accRec w0 p) = ⟨p.command, p.seq, p.deps⟩ ∧ (accRec w0 p).lb = w0.lb := by
    simp [accRec, instVal]
  -- the record at `(i, x)`: old, a fresh default, or the vote
  have hX : (S.rep i).inst x = some w' ∨ ((S.rep i).inst x = none ∧ w' = newInstanceDefault x) ∨
      (w' = accRec w0 p ∧ zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status ∧
        Event.vote x p.ballot stACCEPTED ⟨p.command, p.seq, p.deps⟩ ∈ E) := by
    have h0 : w' = w0 → (S.rep i).inst x = some w' ∨
        ((S.rep i).inst x = none ∧ w' = newInstanceDefault x) := by
      intro he; rw [he]; rcases hro with h | ⟨h, h0⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, h0⟩
    rcases hcase with ⟨he, -⟩ | ⟨he, -⟩ | ⟨h1, h2, h3, hE, -⟩
    · rcases h0 he with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases h0 he with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h1, h2, h3, by rw [hE]; simp⟩)
  -- a new vote only with the vote record
  have hnewv : ∀ b st v, S'.ev i (.vote x b st v) → S.ev i (.vote x b st v) ∨
      (b = p.ballot ∧ st = stACCEPTED ∧ v = ⟨p.command, p.seq, p.deps⟩ ∧ w' = accRec w0 p ∧
        zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status) := by
    intro b st v he
    rcases hev i _ he with h | ⟨-, ⟨c, h⟩ | ⟨h, h1, h2, h3⟩⟩
    · exact Or.inl h
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨-, rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl, h1, h2, h3⟩
  have hvo : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v) ∨
      (r = i ∧ y = x ∧ b = p.ballot ∧ st = stACCEPTED ∧ v = ⟨p.command, p.seq, p.deps⟩ ∧
        w' = accRec w0 p ∧ zz w0.bal ≤ zz p.ballot ∧ ¬ isCommitted w0.status) := by
    intro r y b st v he
    rcases hev r _ he with h | ⟨hr, ⟨c, h⟩ | ⟨h, h1, h2, h3⟩⟩
    · exact Or.inl h
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨hr, rfl, rfl, rfl, rfl, h1, h2, h3⟩
  -- the old record of `w0` when it is old
  have hold0 : (S.rep i).inst x = none → w0 = newInstanceDefault x := by
    intro h; rcases hro with h' | ⟨-, h'⟩
    · rw [h] at h'; cases h'
    · exact h'
  -- records other than `(i, x)`
  have hoth : ∀ r y w, (S'.rep r).inst y = some w → ¬ (r = i ∧ y = x) → (S.rep r).inst y = some w := by
    intro r y w hw hc
    rcases R1 r y w hw with ⟨h1, h2, -⟩ | h
    · exact absurd ⟨h1, h2⟩ hc
    · exact h
  -- the new messages are AcceptReplies
  have hnoP : ∀ (P : Msg → Bool), (∀ c, P (.acceptReply c) = false) →
      ∀ to m, m ∈ snd to ++ intendedOf none to → P m = false := by
    intro P hP to m hm'
    have : m ∈ snd to := by simpa [intendedOf] using hm'
    obtain ⟨-, c, rfl, -⟩ := ctx_snd S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn to m this
    exact hP _
  have hcnt0 : ∀ fr' to (P : Msg → Bool), (∀ c, P (.acceptReply c) = false) →
      S'.cnt fr' to P = S.cnt fr' to P := by
    intro fr' to P hP
    rw [hH.cnt_eq]
    split
    · rw [List.filter_eq_nil_iff.mpr (fun m hm' => by simp [hnoP P hP to m hm'])]; rfl
    · rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- stRange
    intro r hr y w hw
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with h | ⟨-, h⟩ | ⟨h, -, -, -⟩
      · exact hA.stRange r hr y w' h
      · rw [h]; exact Or.inl rfl
      · rw [h, hacR.1]; exact Or.inr (Or.inr (Or.inl rfl))
    · exact hA.stRange r hr y w (hoth r y w hw hc)
  · -- cmdsSome
    intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with h | ⟨-, h⟩ | ⟨h, -, -, -⟩
      · exact hA.cmdsSome r hr y w' h hs
      · rw [h] at hs; exact absurd rfl hs
      · rw [h, hacR.2.2.2.1]; simp
    · exact hA.cmdsSome r hr y w (hoth r y w hw hc) hs
  · -- noneRec
    intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with h | ⟨h0, h⟩ | ⟨h, -, -, -⟩
      · obtain ⟨c1, c2⟩ := hA.noneRec r hr y w' h hs
        refine ⟨c1, fun b st v hv => ?_⟩
        rcases hnewv b st v hv with h1 | ⟨-, -, -, h1, -⟩
        · exact c2 b st v h1
        · rw [h1, hacR.1] at hs; exact absurd hs acc_ne_none
      · refine ⟨by rw [h]; simp [newInstanceDefault], fun b st v hv => ?_⟩
        rcases hnewv b st v hv with h1 | ⟨-, -, -, h1, -⟩
        · exact hnv h0 b st v h1
        · rw [h1, hacR.1] at hs; exact absurd hs acc_ne_none
      · rw [h, hacR.1] at hs; exact absurd hs acc_ne_none
    · obtain ⟨c1, c2⟩ := hA.noneRec r hr y w (hoth r y w hw hc) hs
      refine ⟨c1, fun b st v hv => ?_⟩
      rcases hvo r y b st v hv with h1 | ⟨h1, h2, -⟩
      · exact c2 b st v h1
      · exact hc ⟨h1, h2⟩
  · -- vbalNonneg
    intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with h | ⟨-, h⟩ | ⟨h, -, -, -⟩
      · exact hA.vbalNonneg r hr y w' h hs
      · rw [h] at hs; exact absurd rfl hs
      · rw [h, hacR.2.1]; exact hb0
    · exact hA.vbalNonneg r hr y w (hoth r y w hw hc) hs
  · -- votesLe
    intro r hr y w hw b st v hv
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hnewv b st v hv with h1 | ⟨rfl, -, -, h2, -⟩
      · rcases hX with h | ⟨h0, -⟩ | ⟨h, h2, -, -⟩
        · exact hA.votesLe r hr y w' h b st v h1
        · exact absurd h1 (hnv h0 b st v)
        · rw [h, hacR.2.1]
          rcases hro with h' | ⟨h', -⟩
          · exact Int.le_trans (hA.votesLe r hr y w0 h' b st v h1) (Int.le_trans hvb0 h2)
          · exact absurd h1 (hnv h' b st v)
      · rw [h2, hacR.2.1]; exact Int.le_refl _
    · rcases hvo r y b st v hv with h1 | ⟨h1, h2, -⟩
      · exact hA.votesLe r hr y w (hoth r y w hw hc) b st v h1
      · exact absurd ⟨h1, h2⟩ hc
  · -- recVote
    intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with h | ⟨-, h⟩ | ⟨h, -, -, hE⟩
      · exact hH.ev_old (hA.recVote r hr y w' h hs)
      · rw [h] at hs
        simp [newInstanceDefault, isPA, stNONE, stPREACCEPTED, stPREACCEPTED_EQ, stACCEPTED] at hs
      · rw [h, hacR.2.1, hacR.1, hacR.2.2.2.2.1]
        exact hH.ev_new hE
    · exact hH.ev_old (hA.recVote r hr y w (hoth r y w hw hc) hs)
  · -- accKeep
    intro r hr y w hw b u hv hle
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rcases hX with h | ⟨h0, h⟩ | ⟨h, -⟩
      · rcases hnewv b _ u hv with h1 | ⟨-, -, -, h2, -⟩
        · exact hA.accKeep r hr y w' h b u h1 hle
        · rw [h2, hacR.1]; exact Or.inl rfl
      · rcases hnewv b _ u hv with h1 | ⟨-, -, -, h2, -⟩
        · exact absurd h1 (hnv h0 b _ u)
        · rw [h2, hacR.1]; exact Or.inl rfl
      · rw [h, hacR.1]; exact Or.inl rfl
    · rcases hvo r y b _ u hv with h1 | ⟨h1, h2, -⟩
      · exact hA.accKeep r hr y w (hoth r y w hw hc) b u h1 hle
      · exact absurd ⟨h1, h2⟩ hc
  · -- recCommit
    intro r hr y w hw hs
    have he := ctx_inst_comm S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r y (Or.inr ⟨w, hw, Or.inl hs⟩)
    rw [he] at hw
    obtain ⟨b, v, h1, h2⟩ := hA.recCommit r hr y w hw hs
    exact ⟨b, v, hH.ev_old h1, h2⟩
  · -- commitRec
    intro r y b v hr he
    obtain ⟨w, hw, hs⟩ := hA.commitRec r y b v hr
      (hold r _ he (fun c h => by cases h) (fun h => by cases h))
    exact ⟨w, by rw [ctx_inst_comm S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r y (Or.inl ⟨w, hw, Or.inl hs⟩)]; exact hw, hs⟩
  · -- fastCommitEv
    intro r y v he
    obtain ⟨h1, b, h2⟩ := hA.fastCommitEv r y v (hold r _ he (fun c h => by cases h) (fun h => by cases h))
    exact ⟨h1, b, hH.ev_old h2⟩
  · -- makerLb
    intro r y b hr he
    obtain ⟨w, lb, hw, hlb, hle⟩ := hA.makerLb r y b hr (hold r _ he (fun c h => by cases h) (fun h => by cases h))
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
      rw [(F r).2.2.2.2.2 q]
      split
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
        have := hS.2.crtMsg fr r _ x hpm (by rw [hx]; rfl)
        rw [← hpi] at *
        have h2 := hA.crtOwn r hr x.q hq
        omega
      · exact hA.crtOwn r hr q hq) (hcrt q q)
  · -- crtRec
    intro r hr y w hw
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc
      have := hS.2.crtMsg fr r _ y hpm (by rw [hx]; rfl)
      exact Int.le_trans this (hcrt _ _)
    · exact Int.le_trans (hA.crtRec r hr y w (hoth r y w hw hc)) (hcrt _ _)
  · -- crtMsg
    intro fr' to m y hm' hy
    rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to m hm' with h | ⟨-, -, c, rfl, -⟩
    · exact Int.le_trans (hA.crtMsg fr' to m y h hy) (hcrt _ _)
    · simp only [Msg.instOf, Option.some.injEq] at hy
      rw [← hy, ← hx]
      exact Int.le_trans (hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)) (hcrt _ _)
  · -- crtEv
    intro r e y he hy
    rcases hev r e he with h | ⟨-, ⟨c, rfl⟩ | ⟨rfl, -⟩⟩
    · obtain ⟨c1, c2⟩ := hA.crtEv r e y h hy; exact ⟨c1, Int.le_trans c2 (hcrt _ _)⟩
    · simp [Event.instOf] at hy
    · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
      exact ⟨hxq, Int.le_trans (hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)) (hcrt _ _)⟩
  · -- ownRow
    intro q hq j hj
    rw [hcq] at hj
    obtain ⟨w, lb, hw, hlb⟩ := hA.ownRow q hq j hj
    rcases R2 q _ w hw with ⟨h1, h2, h3⟩ | h
    · rw [h2, h1]; subst h3; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb⟩
    · exact ⟨w, lb, h, hlb⟩
  · -- paNoAcc
    intro r hr y w lb hw hlb hs v hv
    have hv' := hold r _ hv (fun c h => by cases h) (fun h => by cases h)
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
    have hv' := hold r _ hv (fun c h => by cases h) (fun h => by cases h)
    by_cases hcc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw
      have hlb' := hlb
      rw [hlbeq] at hlb
      rcases hX with h | ⟨-, h⟩ | ⟨h, -⟩
      · exact hA.paLeader r hr y w' lb h (by
          rcases hro with h' | ⟨-, h'⟩
          · rw [h] at h'; cases h'; exact hlb
          · rw [h'] at hlb; simp [newInstanceDefault] at hlb) hs ⟨v, hv'⟩ hc hb
      · rw [h] at hlb'; simp [newInstanceDefault] at hlb'
      · exfalso
        rw [h] at hb; simp only [accRec] at hb
        obtain ⟨w1, lb1, hw1, hlb1, -⟩ := hA.makerLb fr y p.ballot hfr hmk
        have hmk' : S.ev r (.makeBallot y lb.lastTriedBallot) := by
          rcases hro with h' | ⟨-, h'⟩
          · exact (hS.1.2.2.2.2.2.2.2.2.2.2.1 r hr y w0 lb h' hlb).1
          · rw [h'] at hlb; simp [newInstanceDefault] at hlb
        rw [← hb] at hmk'
        exact hfi (maker_eq S hS.1.2.2.2.2.2.1 hxq hmk hmk')
    · exact hA.paLeader r hr y w lb (hoth r y w hw hcc) hlb hs ⟨v, hv'⟩ hc hb
  · -- prepNoProp
    intro r hr y w lb hw hlb hp
    have hrel : (S.rep r).inst y = some w ∧ w.lb = some lb ∨
        (r = i ∧ y = x ∧ (S.rep i).inst x = some w0 ∧ w0.lb = some lb) := by
      by_cases hc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
        rw [hlbeq] at hlb
        rcases hro with h | ⟨-, h⟩
        · exact Or.inr ⟨rfl, rfl, h, hlb⟩
        · rw [h] at hlb; simp [newInstanceDefault] at hlb
      · exact Or.inl ⟨hoth r y w hw hc, hlb⟩
    obtain ⟨w1, hw1, hlb1⟩ : ∃ w1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb := by
      rcases hrel with ⟨h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩
      · exact ⟨w, h1, h2⟩
      · exact ⟨w0, h1, h2⟩
    obtain ⟨c1, c2, c3, c4, c5⟩ := hA.prepNoProp r hr y w1 lb hw1 hlb1 hp
    exact ⟨c1, fun v hv => c2 v (hold r _ hv (fun c h => by cases h) (fun h => by cases h)),
      fun v hv => c3 v (hold r _ hv (fun c h => by cases h) (fun h => by cases h)), c4, c5⟩
  · -- paMsgOnce
    intro fr' to y b; rw [hcnt0 fr' to _ (fun c => rfl)]; exact hA.paMsgOnce fr' to y b
  · -- accMsgOnce
    intro fr' to y b; rw [hcnt0 fr' to _ (fun c => rfl)]; exact hA.accMsgOnce fr' to y b
  · -- paVoteDeliv
    intro r y b st v hst hv
    rcases hvo r y b st v hv with h | ⟨-, -, -, rfl, -⟩
    · rcases hA.paVoteDeliv r y b st v hst h with ⟨v0, h1⟩ | h1
      · exact Or.inl ⟨v0, hH.ev_old h1⟩
      · exact Or.inr (fun fr' => hH.allDeliv_old (h1 fr') (fun _ m hm' => hnoP _ (fun c => rfl) _ m hm'))
    · exact absurd hst acc_not_pa
  · -- parOnce
    intro a r y b h1
    rw [hcnt0 a r _ (fun c => rfl)] at h1 ⊢
    obtain ⟨c1, c2⟩ := hA.parOnce a r y b h1
    exact ⟨c1, hH.allDeliv_old c2 (fun _ m hm' => hnoP _ (fun c => rfl) _ m hm')⟩
  · -- arFrom
    intro a r m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn a r _ hm' with h | ⟨-, hr, c, hmc, hcb, -⟩
    · obtain ⟨b', v, h1, h2⟩ := hA.arFrom a r m h; exact ⟨b', v, h1, hH.ev_old h2⟩
    · simp only [Msg.acceptReply.injEq] at hmc; subst hmc hr
      refine ⟨p.ballot, ⟨p.command, p.seq, p.deps⟩, hcb, ?_⟩
      simp only; rw [← hx]; exact hH.ev_old hacc
  · -- arOnce
    intro a r y b h1
    have habove : S.lastAbove r y b → S'.lastAbove r y b := by
      rintro ⟨w, lb, hw, hlb, hlt⟩
      rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
      · subst r y w; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb, hlt⟩
      · exact ⟨w, lb, h, hlb, hlt⟩
    rw [hH.cnt_eq] at h1 ⊢
    by_cases hnew : a = i ∧ ((snd r ++ intendedOf none r).filter (Msg.isARat y b)).length ≠ 0
    · obtain ⟨ha, hne⟩ := hnew
      subst a
      obtain ⟨m, hmf⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hne))
      have hmf' := List.mem_filter.mp hmf
      have hmsnd : m ∈ snd r := by simpa [intendedOf] using hmf'.1
      obtain ⟨hr, c, hmc, hcb, -, hcs⟩ := ctx_snd S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r m hmsnd
      subst r hmc
      simp only [Msg.isARat, decide_eq_true_eq] at hmf'
      obtain ⟨-, hy, hcb'⟩ := hmf'
      subst hcb'
      rw [← hx] at hy; subst y
      by_cases hlt : zz c < zz p.ballot
      · obtain ⟨w, lb, hw, hlb, hle⟩ := hA.makerLb fr x p.ballot hfr hmk
        refine Or.inl ⟨w, lb, ?_, hlb, Int.lt_of_lt_of_le hlt hle⟩
        rw [R4 fr x (Or.inl hfi)]; exact hw
      · have hcp : c = p.ballot := zz_inj (by omega)
        subst hcp
        -- no older AcceptReply at this ballot: the Accept at it was undelivered
        rcases Nat.eq_zero_or_pos (S.cnt i fr (Msg.isARat x p.ballot)) with h0 | hpos
        · have hsf : snd fr = [.acceptReply ⟨p.replica, p.inst, p.ballot⟩] := by
            rcases hcase with ⟨-, -, h⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
            · rw [h] at hmsnd; cases hmsnd
            · rw [h] at hmsnd ⊢; simp only [if_true, List.mem_singleton] at hmsnd ⊢
              rw [← hmsnd]
            · rw [h]; simp
          refine Or.inr ⟨?_, fun n' m' hn' hp' => ?_⟩
          · rw [h0, hsf]; simp [intendedOf, Msg.isARat, hx]
          · rw [hH.msgs, if_neg hfi, List.append_nil] at hn'
            have := pos_unique _ _ (hA.accMsgOnce fr i x p.ballot) hn' hp' (msgs_of_sent S hm)
              (by simp [Msg.isAccAt, hx])
            rw [this]; exact hdn
        · rcases hA.arOnce i fr x p.ballot hpos with h | ⟨-, h⟩
          · exact Or.inl (habove h)
          · exact absurd (h n _ (msgs_of_sent S hm) (by simp [Msg.isAccAt, hx])) hn
    · have hz : (if a = i then ((snd r ++ intendedOf none r).filter (Msg.isARat y b)).length
          else 0) = 0 := by
        split
        · rename_i ha; exact Classical.byContradiction fun h => hnew ⟨ha, h⟩
        · rfl
      rw [hz, Nat.add_zero] at h1 ⊢
      rcases hA.arOnce a r y b h1 with h | ⟨h2, h3⟩
      · exact Or.inl (habove h)
      · exact Or.inr ⟨h2, hH.allDeliv_old h3 (fun _ m hm' => hnoP _ (fun c => rfl) _ m hm')⟩
  · -- commitBal
    intro fr' to m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to _ hm' with h | ⟨-, -, c, h, -⟩
    · exact hA.commitBal fr' to m h
    · cases h
  · -- sentPR
    intro r to m he
    have he0 := hold r _ he (fun c h => by cases h) (fun h => by cases h)
    obtain ⟨c1, c2, c3⟩ := hA.sentPR r to m he0
    refine ⟨fun hr => ?_, fun b st v hb => ?_, fun to' m2 hb hy => ?_⟩
    · obtain ⟨w, hw, hle⟩ := c1 hr
      rcases R2 r _ w hw with ⟨h1, h2, h3⟩ | h
      · subst r w; rw [h2]; exact ⟨w', R3, Int.le_trans hle hwb⟩
      · exact ⟨w, h, hle⟩
    · rcases (hH.evBefore_iff _ _ _ _).mp hb with h1 | ⟨-, hr, h1⟩ | ⟨hr, -, pp, pp', -, h1, -⟩
      · exact c2 b st v h1
      · subst r
        rcases ctx_E S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ h1 with ⟨c, h⟩ | ⟨h, -, h2, -⟩
        · cases h
        · simp only [Event.vote.injEq] at h; obtain ⟨hy, hb', -, -⟩ := h
          obtain ⟨w, hw, hle⟩ := c1 hi
          rw [hy] at hw
          rcases hro with h' | ⟨h', -⟩
          · rw [h'] at hw; cases hw; rw [hb']; exact Int.le_trans hle h2
          · rw [h'] at hw; cases hw
      · exfalso
        rcases ctx_E S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ (List.mem_of_getElem? h1) with ⟨c, h⟩ | ⟨h, -⟩
        · cases h
        · cases h
    · rcases (hH.evBefore_iff _ _ _ _).mp hb with h1 | ⟨-, hr, h1⟩ | ⟨hr, -, pp, pp', -, h1, -⟩
      · exact c3 to' m2 h1 hy
      · subst r
        obtain ⟨-, c, hmc, hc⟩ := ctx_sentE S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ _ h1
        simp only [Msg.acceptReply.injEq] at hmc; subst hmc
        obtain ⟨w, hw, hle⟩ := c1 hi
        rw [← hy, ← hx] at hw
        rcases hro with h' | ⟨h', -⟩
        · rw [h'] at hw; cases hw; exact Int.le_trans hle hc
        · rw [h'] at hw; cases hw
      · exfalso
        rcases ctx_E S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn _ (List.mem_of_getElem? h1) with ⟨c, h⟩ | ⟨h, -⟩
        · cases h
        · cases h
  · -- confCover
    intro r hr e y cy he hrec c hc
    rw [(F r).2.2.1]
    exact hA.confCover r hr e y cy (hold r e he (fun c h => by subst h; simp [Event.recorded] at hrec)
      (fun h => by subst h; simp [Event.recorded] at hrec)) hrec c hc
  · -- classWf
    have hcl : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧
        (S'.rep r).lastPut = (S.rep r).lastPut := by
      intro r; rw [hH.rep]; by_cases h : r = i
      · subst h; simp only [upd_same, RState.setInst]
        exact ⟨by rw [(AuxProof.bumpCrt_cls _ _ _).1, (AuxProof.bumpRB_cls _ _).1],
          by rw [(AuxProof.bumpCrt_cls _ _ _).2, (AuxProof.bumpRB_cls _ _).2]⟩
      · simp [upd_apply, h]
    intro r hr
    refine AuxProof.clsWf_keep (hA.classWf r hr) (hcl r).1 (hcl r).2 (fun y h => ?_)
    obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp h
    rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h2
    · rw [R3]; simp
    · rw [h2]; simp
  · -- classCover
    have hcl : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧
        (S'.rep r).lastPut = (S.rep r).lastPut := by
      intro r; rw [hH.rep]; by_cases h : r = i
      · subst h; simp only [upd_same, RState.setInst]
        exact ⟨by rw [(AuxProof.bumpCrt_cls _ _ _).1, (AuxProof.bumpRB_cls _ _).1],
          by rw [(AuxProof.bumpCrt_cls _ _ _).2, (AuxProof.bumpRB_cls _ _).2]⟩
      · simp [upd_apply, h]
    intro r hr e y cy he hrec
    rw [(hcl r).1, (hcl r).2]
    exact hA.classCover r hr e y cy (hold r e he (fun c h => by subst h; simp [Event.recorded] at hrec)
      (fun h => by subst h; simp [Event.recorded] at hrec)) hrec
  · -- paAttrs
    intro r y b st v hst hv
    rcases hvo r y b st v hv with h | ⟨-, -, -, rfl, -⟩
    · exact hH.ev_old (hA.paAttrs r y b st v hst h)
    · exact absurd hst acc_not_pa
  · -- valOk
    intro r y b v hv
    rw [hH.owner]
    exact hA.valOk r y b v (hv.imp (fun h => hold r _ h (fun c h => by cases h) (fun h => by cases h))
      (fun h => hold r _ h (fun c h => by cases h) (fun h => by cases h)))
  · -- cmdsNe
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
    refine ⟨fun fr' to m hm' cs hc => ?_, fun r hr y w cs hw hc => ?_,
      fun r hr y w lb cs hw hlb hc => ?_, fun fr' to m hm' hs => ?_,
      fun r m he => n5 r m (hold r _ he (fun c h => by cases h) (fun h => by cases h)),
      fun r y b v hv => n6 r y b v (hv.imp (fun h => hold r _ h (fun c h => by cases h) (fun h => by cases h))
        (fun h => hold r _ h (fun c h => by cases h) (fun h => by cases h)))⟩
    · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to m hm' with h | ⟨-, -, c, rfl, -⟩
      · exact n1 fr' to m h cs hc
      · cases hc
    · by_cases hcc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw
        rcases hX with h | ⟨-, h⟩ | ⟨h, -⟩
        · exact n2 r hr y w' cs h hc
        · rw [h] at hc; simp [newInstanceDefault] at hc
        · rw [h, hacR.2.2.2.1] at hc; simp only [Option.some.injEq] at hc; subst hc
          exact n1 fr r _ hpm _ rfl
      · exact n2 r hr y w cs (hoth r y w hw hcc) hc
    · by_cases hcc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw
        rw [hlbeq] at hlb
        rcases hro with h | ⟨-, h⟩
        · exact n3 r hr y w0 lb cs h hlb hc
        · rw [h] at hlb; simp [newInstanceDefault] at hlb
      · exact n3 r hr y w lb cs (hoth r y w hw hcc) hlb hc
    · rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to _ hm' with h | ⟨-, -, c, h, -⟩
      · exact n4 fr' to m h hs
      · cases h
  · -- prSent
    intro fr' to m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to _ hm' with h | ⟨-, -, c, h, -⟩
    · exact hH.ev_old (hA.prSent fr' to m h)
    · cases h
  · -- selfOk
    intro r m he hs
    exact hA.selfOk r m (hold r _ he (fun c h => by cases h) (fun h => by cases h)) hs
  · -- selfRaw
    intro r m he
    exact hA.selfRaw r m (hold r _ he (fun c h => by cases h) (fun h => by cases h))
  · -- pm (sixth agent)
    have hP := hA.pm
    have hmo := ctx_mono S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
    have hcv := ctx_cv S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
    have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
    have hacc' : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v) :=
      fun r y b v h => hold r _ h (fun c h => by cases h) (fun h => by cases h)
    have hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v) :=
      fun r y b v h => hold r _ h (fun c h => by cases h) (fun h => by cases h)
    have hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
      fun r y c u h => hold r _ h (fun c h => by cases h) (fun h => by cases h)
    have hvpa : ∀ r y b st v, isPA st → S'.ev r (.vote y b st v) → S.ev r (.vote y b st v) := by
      intro r y b st v hst h
      rcases hvo r y b st v h with h | ⟨-, -, -, rfl, -⟩
      · exact h
      · exact absurd hst acc_not_pa
    have hmsg : ∀ fr' to m, m ∈ S'.msgs fr' to → (∀ c, m ≠ .acceptReply c) →
        m ∈ S.msgs fr' to := by
      intro fr' to m h hn'
      rcases ctx_msgs S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn fr' to m h with h | ⟨-, -, c, rfl, -⟩
      · exact h
      · exact absurd rfl (hn' _)
    have hsent : ∀ fr to m, m ∈ S.sent fr to → m ∈ S'.sent fr to := by
      intro fr to m h; rw [hH.sent]; exact h
    have hlb0 : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
        ∃ w, (S.rep r).inst y = some w ∧ w.lb = some lb2 := by
      intro r y w2 lb2 hw hl
      by_cases hc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
        rw [hlbeq] at hl
        rcases hro with h | ⟨-, h⟩
        · exact ⟨w0, h, hl⟩
        · rw [h] at hl; simp [newInstanceDefault] at hl
      · exact ⟨w2, hoth r y w2 hw hc, hl⟩
    have hlb : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
        ∃ w lb, (S.rep r).inst y = some w ∧ w.lb = some lb ∧ PMProof.LbPM lb lb2 := by
      intro r y w2 lb2 hw hl
      obtain ⟨w, h1, h2⟩ := hlb0 r y w2 lb2 hw hl
      exact ⟨w, lb2, h1, h2, PMProof.LbPM.refl _⟩
    have hPAR : ∀ a r m, Msg.preAcceptReply m ∈ S'.msgs a r → Msg.preAcceptReply m ∈ S.msgs a r :=
      fun a r m h => hmsg _ _ _ h (fun c h => by cases h)
    exact {
      arOk := ctx_arOk S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn
      commitProp := PMProof.commitProp_frame hP hcm hmono
      commitMsgProp := PMProof.commitMsgProp_frame hP
        (fun fr to m h => hmsg _ _ _ h (fun c h => by cases h)) hmono
      lbProp := PMProof.lbProp_frame hP hlb hacc' hmono
      parCom := PMProof.parCom_frame hP hPAR hmono
      parSt := PMProof.parSt_frame hP hPAR hsent
      paFresh := PMProof.paFresh_frame hP hlb hph
      paCmds := PMProof.paCmds_frame hP hlb hph
      paSent := PMProof.ps_hs hP hH hidle.1
        (fun to m h y => by
          obtain ⟨-, c, rfl, -⟩ := ctx_snd S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn to m h
          rfl)
        (fun b h => by cases h)
        (fun y w2 lb2 hw hl hlt => by
          obtain ⟨w, h1, h2⟩ := hlb0 _ y w2 lb2 hw hl
          exact ⟨w, lb2, h1, h2, hlt, rfl⟩)
      pendPA := PMProof.pendPA_hs hP hH (fun b h => by cases h)
      paVoteMsg := fun r y st v hst hne h => by
        obtain ⟨q, h1, h2, h3⟩ := hP.paVoteMsg r y st v hst hne (hvpa _ _ _ _ _ hst h)
        exact ⟨q, hsent _ _ _ h1, h2, h3⟩
      parNoPA := fun a r m hm' hn' st u hst h =>
        hP.parNoPA a r m (hPAR _ _ _ hm') hn' st u hst (hvpa _ _ _ _ _ hst h)
      aeF := PMProof.aeF_frame hP hlb hsent
      repLead := PMProof.repLead_frame hP
        (fun r m e h => (ctx_prep S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn r m e h).1)
        (fun r y w h => by
          obtain ⟨w', h1, h2, -⟩ := hmo.bal r y w h
          exact ⟨w', h1, h2⟩)
      paGe := fun r y b st v ℓ v0 hst h1 h2 =>
        hP.paGe r y b st v ℓ v0 hst (hvpa _ _ _ _ _ hst h1) (hph _ _ _ _ h2)
      phAttrs := PMProof.phAttrs_frame hP hph hmono
      accWit := PMProof.accWit_frame hP hacc' hmono (fun y u h => (hcv _ _).mpr h)
      accVote := PMProof.accVote_frame hP hacc' hmono
      cmdSafe := CmdSafeProof.cmdSafe_frame hP hmo hph
      accSup := CmdSafeProof.accSup_frame hP hmono hacc' }
  · -- ownerCrt (p-model2)
    intro y ps h; rw [hH.owner] at h
    obtain ⟨h1, h2⟩ := hA.ownerCrt y ps h
    exact ⟨h1, Int.le_trans h2 (hcrt _ _)⟩
  · -- execLo (p-exec)
    exact AuxProof.execLo_of_eq hS.2.execLo (fun r _ => (F r).2.2.2.1)
  · -- execution fields (p-modelexec)
    refine ExecOrd.invExec_hs hS.1 hS.2.exec hH hidle (ctx_agr S S' fr i n p x w0 w' E snd hS hi hfr hidle hn hm hx hH hro hcase hdn) hchan R4 R3
      (fun w hw hs => ?_) (fun lb' hl hne => ?_)
    · rcases hro with h | ⟨h, -⟩
      · rw [h] at hw; cases hw; rw [hweq (Or.inr hs)]
      · rw [h] at hw; cases hw
    · rw [hlbeq] at hl
      rcases hro with h | ⟨-, h⟩
      · exact ⟨w0, lb', h, hl, hne⟩
      · subst h; simp [newInstanceDefault] at hl

end


/-- **`handleAccept` keeps the invariant.** -/
theorem inv_deliver_accept' (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : Accept)
    (hm : (S.sent fr i)[n]? = some (.accept p)) : Inv (S.deliver fr i n (.accept p)) := by
  have hpm := mem_msgs_of_sent S hm
  obtain ⟨hldr, -⟩ := hS.1.2.2.2.2.2.1.2.2.2.2.2 fr i p hpm
  have hc := accept_cases S fr i n p hidle hm hfr hldr (fun x w h => hS.2.stRange i hi x w h)
  dsimp only at hc
  have hro := recOr_of (S.rep i) ⟨toN p.replica, toN p.inst⟩
  have hdn := deliver_delivered S fr i n (.accept p)
  generalize recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩ = w0 at hc hro
  obtain ⟨w', E, snd, hH, hcase⟩ := hc
  have hwf := ctx_wf S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn
  have hbal := ctx_ballots S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn
  have hown := ctx_own S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn
  have hvf := ctx_vf S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn
  have hsafe := ctx_safe S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn
  obtain ⟨e1, e2, e3, e4⟩ := ctx_exec S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn
  exact ⟨⟨hwf, ctx_msgWf S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_rt S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_ntpa S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, hbal, hown, ctx_op S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, hvf, ctx_rr S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn,
    ctx_hi S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_lb S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_agr S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_dc S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, chosenSafe_of_safe _ hwf hbal hown hvf hsafe,
    ctx_dcv S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_wit S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_ac S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, e1, e2, e3, e4, ctx_slots S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_co S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, ctx_cm S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn,
    ctx_pk S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn, hsafe, ctx_reports S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn⟩, ctx_aux S _ fr i n p _ w0 w' E snd hS hi hfr hidle hn hm rfl hH hro hcase hdn (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h))⟩

end AcceptProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
