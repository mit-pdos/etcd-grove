/-
The riskiest step of the model: the recovery's decision (`handlePrepareReply` on its `(N+1)/2`-th
distinct reply at its ballot `n`, `prepDecide`) is safe. If it proposes (sub-case 2 or 3: an
Accept at `n` of the chosen reply's value), the Accept is `safeAcc`; if it starts a Phase 1
(sub-cases 5, 6), the Phase 1 is `safePh` (`Inv.safe`). Stated over the pre-state `S`, from `Inv S`
and the report facts `DecAux` (to be conjuncts), for any list of replies that are reports at `n`
of distinct replicas about `x` (what `Inv.lbInv` says of `lb.prepareReplies` plus the delivered
reply).

Paper proof (with fix R-PROM, G1): every reporter promised `n` (`bal ≥ n`, `reportBal`) and voted
below `n` only before its report, at most at its reported `vballot ≤ maxVbal`. So above `maxVbal`
the reporters block every value; at `maxVbal` they block every value they did not report as
ACCEPTED there (`reportAcc`); below `maxVbal` the proposal at `maxVbal` (the reported vote's
Accept or Phase 1) was safe (induction: `Inv.safe S`). Fast path: a reported Accept/Phase 1 above
the initial ballot was safe; an Accept at the initial ballot is the leader's slow path
(`accInit`); else the leader reported (then it never fast-commits: `fastReported`) or the
reporters are non-leaders of which at most one pre-accepted any given value (two would make
sub-case 3 apply).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Safe
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxDefs

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace DecideProof

open SafeProof

/-- The report facts the decision needs (planned conjuncts, `Proof/AuxDefs.lean`). -/
structure DecAux (S : Sys) : Prop where
  status : Aux.reportStatus S
  none : Aux.reportNone S
  deps : Aux.reportDeps S
  acc : Aux.reportAcc S
  bal : Aux.reportBal S
  pa : Aux.paUnique S
  fast : Aux.fastReported S
  accInit : Aux.accInit S
  vbal : ∀ r m e, S.prepReport r m e → zz m.vballot ≤ zz m.ballot

/-- The conjunct `Inv.reports` gives the decision's report facts. -/
theorem decAux_of {S : Sys} (h : Inv.reports S) : DecAux S :=
  let ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := h
  ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩

/-! ## Generic facts -/

theorem ev_split (S : Sys) {r : Nat} {e1 e2 : Event} (h1 : S.ev r e1) (h2 : S.ev r e2)
    (hne : e1 ≠ e2) : S.evBefore r e1 r e2 ∨ S.evBefore r e2 r e1 := by
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp h1
  obtain ⟨p', hp'⟩ := List.mem_iff_getElem?.mp h2
  rcases Nat.lt_trichotomy p p' with h | h | h
  · exact Or.inl ⟨p, p', h, hp, hp'⟩
  · subst h; rw [hp] at hp'
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hp'
    exact absurd hp' hne
  · exact Or.inr ⟨p', p, h, hp', hp⟩

/-- `maxVbal`'s fold. -/
def maxStep (mx : w32) (e : PReply) : w32 := if mx.slt e.m.vballot then e.m.vballot else mx

theorem foldl_max (l : List PReply) (init : w32) :
    zz init ≤ zz (l.foldl maxStep init) ∧ (∀ e ∈ l, zz e.m.vballot ≤ zz (l.foldl maxStep init)) ∧
    (l.foldl maxStep init = init ∨ ∃ e ∈ l, e.m.vballot = l.foldl maxStep init) := by
  induction l generalizing init with
  | nil => exact ⟨Int.le_refl _, by simp, Or.inl rfl⟩
  | cons e l ih =>
    simp only [List.foldl_cons]
    obtain ⟨i1, i2, i3⟩ := ih (maxStep init e)
    have hst : zz init ≤ zz (maxStep init e) ∧ zz e.m.vballot ≤ zz (maxStep init e) ∧
        (maxStep init e = init ∨ maxStep init e = e.m.vballot) := by
      unfold maxStep
      split
      · rename_i h; rw [BitVec.slt_eq_decide] at h; simp only [decide_eq_true_eq] at h
        exact ⟨Int.le_of_lt h, Int.le_refl _, Or.inr rfl⟩
      · rename_i h; rw [BitVec.slt_eq_decide] at h; simp only [decide_eq_true_eq] at h
        exact ⟨Int.le_refl _, by simp only [zz, sint.Z]; omega, Or.inl rfl⟩
    refine ⟨Int.le_trans hst.1 i1, fun e' he' => ?_, ?_⟩
    · rcases List.mem_cons.mp he' with rfl | h
      · exact Int.le_trans hst.2.1 i1
      · exact i2 e' h
    · rcases i3 with h | ⟨e', he', h⟩
      · rcases hst.2.2 with h' | h'
        · exact Or.inl (h.trans h')
        · exact Or.inr ⟨e, List.mem_cons_self, by rw [h, h']⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h⟩

theorem depsEqual_self (d : List w32) : depsEqual d d = true := by
  simp [depsEqual]

theorem depsEqual_eq {d d' : List w32} (hl : d.length = d'.length) (h : depsEqual d d' = true) :
    d = d' := by
  apply List.ext_getElem hl
  intro i h1 h2
  simp only [depsEqual, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h i h1
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using this

theorem filter_len {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun a => ¬ p a)).length = l.length := by
  have := List.length_eq_countP_add_countP p (l := l)
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at this
  omega

theorem two_le_of_mem {α : Type} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    2 ≤ l.length := by
  match l, ha, hb with
  | [], ha, _ => cases ha
  | [c], ha, hb =>
    simp only [List.mem_singleton] at ha hb; exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _, _, _ => simp

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_map_of_mem ha), nodup_of_map f h.2⟩

theorem le_one_of_eq {l : List Nat} (hl : l.Nodup) (c : Nat) (h : ∀ a ∈ l, a = c) :
    l.length ≤ 1 := by
  match l, hl, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: _, hl, h =>
    have h1 := h a List.mem_cons_self
    have h2 := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [List.nodup_cons, List.mem_cons, not_or] at hl
    exact absurd (h1.trans h2.symm) hl.1.1

theorem notCommitted_of_stGe {s : w8} (h : stGe s stCOMMITTED = false) : ¬ isCommitted s := by
  unfold isCommitted stGe at *; rintro (rfl | rfl) <;> revert h <;> decide

theorem stGe_of_committed {s : w8} (h : isCommitted s) : stGe s stCOMMITTED = true := by
  unfold isCommitted stGe at *; rcases h with rfl | rfl <;> decide

/-! ## The decision's cases -/

/-- What `prepDecide` returned. -/
theorem prepDecide_cases (reps : List PReply) (mx : w32) (lr : Bool) (rep : w32) :
    let d := prepDecide reps mx lr rep
    d.1 = 1 ∨
    ((∀ e ∈ reps, stGe e.m.status stCOMMITTED = false) ∧
      ((d.1 = 2 ∧ ∃ e, d.2 = some e ∧ e ∈ reps ∧ e.m.vballot = mx ∧ e.m.status = stACCEPTED) ∨
       ((∀ e ∈ reps, ¬ (e.m.vballot = mx ∧ e.m.status = stACCEPTED)) ∧
        ((d.1 = 3 ∧ isInitialBallot mx rep = true ∧ lr = false ∧
           ∃ e, d.2 = some e ∧ e ∈ reps ∧ subCase3Ok reps mx e = true) ∨
         (d.1 ≠ 1 ∧ d.1 ≠ 2 ∧ d.1 ≠ 3 ∧
           (isInitialBallot mx rep = true → lr = false →
             ∀ e ∈ reps, subCase3Ok reps mx e = false)))))) := by
  simp only [prepDecide]
  split
  · exact Or.inl rfl
  · rename_i h1
    rw [List.find?_eq_none] at h1
    refine Or.inr ⟨fun e he => by simpa using h1 e he, ?_⟩
    split
    · rename_i e he
      have := List.find?_some he
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact Or.inl ⟨rfl, e, rfl, List.mem_of_find?_eq_some he, this.1, this.2⟩
    · rename_i h2
      rw [List.find?_eq_none] at h2
      refine Or.inr ⟨fun e he hc => h2 e he (by simp [hc.1, hc.2]), ?_⟩
      split
      · rename_i e he
        split at he
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          exact Or.inl ⟨rfl, hc.1, hc.2, e, rfl, List.mem_of_find?_eq_some he, List.find?_some he⟩
        · cases he
      · rename_i h3
        refine Or.inr ⟨?_, ?_, ?_, fun hi hl e he => ?_⟩
        · split <;> simp
        · split <;> simp
        · split <;> simp
        · rw [if_pos (by simp [hi, hl] : (isInitialBallot mx rep && !lr) = true)] at h3
          rw [List.find?_eq_none] at h3
          simpa using h3 e he

/-! ## Reports at the recovery's ballot -/

/-- `reps` are reports at `n` about `x` of distinct replicas, a majority. -/
structure Reports (S : Sys) (x : InstId) (n : w32) (reps : List PReply) : Prop where
  nodup : (reps.map (·.m.acceptorId)).Nodup
  len : (nR + 1) / 2 ≤ reps.length
  mem : ∀ e ∈ reps, toN e.m.acceptorId < nR ∧ e.m.ballot = n ∧ e.m.replica = W32 x.q ∧
    Aux.repX e.m = x ∧ ∃ E, S.prepReport (toN e.m.acceptorId) e.m E

section
variable {S : Sys} {x : InstId} {n : w32} {reps : List PReply}

theorem rep_vote (hrr : Inv.repliesReportVotes S) (hhi : Inv.prepReplyHighest S)
    {e : PReply} {E : Event} (hn : e.m.ballot = n) (hx : Aux.repX e.m = x)
    (hE : S.prepReport (toN e.m.acceptorId) e.m E) {b : w32} {st : w8} {u : Val}
    (hv : S.ev (toN e.m.acceptorId) (.vote x b st u)) (hb : zz b < zz n) :
    S.evBefore (toN e.m.acceptorId) (.vote x b st u) (toN e.m.acceptorId) E ∧
      zz b ≤ zz e.m.vballot := by
  have hne : Event.vote x b st u ≠ E := by
    rcases hE.2 with ⟨to, -, rfl⟩ | rfl <;> intro h <;> cases h
  rcases ev_split S hv hE.1 hne with h | h
  · refine ⟨h, ?_⟩
    have := hhi _ e.m E hE b st u
    simp only [Aux.repX] at hx; rw [hx] at this
    exact this h
  · have := (hrr.1 _ e.m E hE).2.2.2.2 b st u
    simp only [Aux.repX] at hx; rw [hx] at this
    have := this h; rw [hn] at this; omega

theorem acc_eq (hrr : Inv.repliesReportVotes S) {e : PReply} {E : Event}
    (hE : S.prepReport (toN e.m.acceptorId) e.m E) : e.m.acceptorId = W32 (toN e.m.acceptorId) :=
  (hrr.1 _ e.m E hE).1

theorem reps_nodup (hrr : Inv.repliesReportVotes S) (hR : Reports S x n reps)
    {l : List PReply} (hl : l.Sublist reps) : (l.map (fun e => toN e.m.acceptorId)).Nodup := by
  have h1 : (l.map (·.m.acceptorId)).Nodup := (hl.map _).nodup hR.nodup
  have : l.map (fun e => toN e.m.acceptorId) = (l.map (·.m.acceptorId)).map toN := by
    simp [List.map_map, Function.comp_def]
  rw [this]
  refine FromMathlib.Nodup.map_on ?_ h1
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  obtain ⟨e1, he1, rfl⟩ := ha
  obtain ⟨e2, he2, rfl⟩ := hb
  obtain ⟨-, -, -, -, E1, hE1⟩ := hR.mem e1 (hl.subset he1)
  obtain ⟨-, -, -, -, E2, hE2⟩ := hR.mem e2 (hl.subset he2)
  rw [acc_eq hrr hE1, acc_eq hrr hE2, hab]

/-- The reporters block `w` at `b < n` if none of them voted ACCEPTED for it at `b`. -/
theorem blocked_reps (hrr : Inv.repliesReportVotes S) (hA : DecAux S) (hR : Reports S x n reps)
    {b : w32} {w : Val} (hb : zz b < zz n)
    (hno : ∀ e ∈ reps, ¬ S.ev (toN e.m.acceptorId) (.vote x b stACCEPTED w)) :
    S.blocked x b w := by
  refine ⟨reps.map (fun e => toN e.m.acceptorId), reps_nodup hrr hR (List.Sublist.refl _), ?_,
    fun a ha => ?_⟩
  · simp only [List.length_map]; have := hR.len; simp only [nR] at this ⊢; omega
  · simp only [List.mem_map] at ha
    obtain ⟨e, he, rfl⟩ := ha
    obtain ⟨han, hn, -, hx, E, hE⟩ := hR.mem e he
    obtain ⟨wa, hwa, hle⟩ := hA.bal _ e.m E han hE
    rw [hx, hn] at *
    exact ⟨han, hno e he, wa, hwa, by omega⟩

/-- Above the highest reported `vballot` (and below `n`) the reporters block every value. -/
theorem blocked_above (hrr : Inv.repliesReportVotes S) (hhi : Inv.prepReplyHighest S)
    (hA : DecAux S) (hR : Reports S x n reps) {b : w32} (hb : zz b < zz n)
    (hmx : zz (reps.foldl maxStep (W32 (-1))) < zz b) (w : Val) : S.blocked x b w := by
  refine blocked_reps hrr hA hR hb (fun e he hv => ?_)
  obtain ⟨-, hn, -, hx, E, hE⟩ := hR.mem e he
  have := (rep_vote hrr hhi hn hx hE hv hb).2
  have := (foldl_max reps (W32 (-1))).2.1 e he
  omega

/-- At the highest reported `vballot`, if no reply is committed or ACCEPTED there, the reporters
block every value. -/
theorem blocked_at_max (hrr : Inv.repliesReportVotes S) (hhi : Inv.prepReplyHighest S)
    (hA : DecAux S) (hR : Reports S x n reps) (hmn : zz (reps.foldl maxStep (W32 (-1))) < zz n)
    (hnc : ∀ e ∈ reps, stGe e.m.status stCOMMITTED = false)
    (hna : ∀ e ∈ reps, ¬ (e.m.vballot = reps.foldl maxStep (W32 (-1)) ∧ e.m.status = stACCEPTED))
    (w : Val) : S.blocked x (reps.foldl maxStep (W32 (-1))) w := by
  refine blocked_reps hrr hA hR hmn (fun e he hv => ?_)
  obtain ⟨-, hn, -, hx, E, hE⟩ := hR.mem e he
  obtain ⟨hbef, hle⟩ := rep_vote hrr hhi hn hx hE hv hmn
  have hge := (foldl_max reps (W32 (-1))).2.1 e he
  have heq : e.m.vballot = reps.foldl maxStep (W32 (-1)) := zz_inj (by omega)
  have := hA.acc _ e.m E hE _ w (by rw [hx]; exact hbef) (by omega)
  rcases this with h | h
  · exact hna e he ⟨heq, h⟩
  · exact notCommitted_of_stGe (hnc e he) h

theorem real_of_make (hown : Inv.ballotOwner S) (hxq : x.q < nR) {ℓ : Nat} {b : w32}
    (h : S.ev ℓ (.makeBallot x b)) : realBal x b := by
  rcases (hown.1 ℓ x b h).1 with ⟨h1, -⟩ | ⟨h1, -⟩
  · refine Or.inl ?_
    unfold initBal
    exact eq_W32_of_zz b x.q (by omega) (by simp [nR] at hxq; omega) h1
  · exact Or.inr h1

theorem zz_real (hxq : x.q < nR) {b : w32} (h : realBal x b) : 0 ≤ zz b ∧
    (zz b ≤ zz (initBal x) → b = initBal x) := by
  rw [zz_initBal x hxq]
  rcases h with rfl | h
  · rw [zz_initBal x hxq]; exact ⟨by omega, fun _ => rfl⟩
  · simp [nR] at hxq h ⊢; exact ⟨by omega, fun h' => by omega⟩

/-- The value a PA/ACCEPTED report reports is a vote of its replica before the report. -/
theorem rep_reported (hrr : Inv.repliesReportVotes S) {e : PReply} {E : Event}
    (hx : Aux.repX e.m = x) (hE : S.prepReport (toN e.m.acceptorId) e.m E)
    (hs : isPA e.m.status ∨ e.m.status = stACCEPTED) :
    S.ev (toN e.m.acceptorId) (.vote x e.m.vballot e.m.status ⟨e.m.command, e.m.seq, e.m.deps⟩) := by
  have := (hrr.1 _ e.m E hE).2.1 hs
  simp only [Aux.repX] at hx; rw [hx] at this
  obtain ⟨p, p', -, hp, -⟩ := this
  exact List.mem_of_getElem? hp

section
variable (hI : Inv0 S) (hA : DecAux S) (hxq : x.q < nR) (hn : (nR : Int) ≤ zz n)
  (hR : Reports S x n reps)
include hI hA hxq hn hR

theorem safe_sub2 {e : PReply} (he : e ∈ reps)
    (hev : e.m.vballot = reps.foldl maxStep (W32 (-1))) (hes : e.m.status = stACCEPTED) :
    S.safeAcc x n ⟨e.m.command, e.m.seq, e.m.deps⟩ := by
  obtain ⟨hwf, -, -, -, -, hown, hop, hvf, hrr, hhi, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsafe, -⟩ := hI
  obtain ⟨han, hn', hrep, hx, E, hE⟩ := hR.mem e he
  have hv := rep_reported hrr hx hE (Or.inr hes)
  rw [hes, hev] at hv
  obtain ⟨ℓ0, hacc⟩ := hvf.2 _ x _ _ hv
  have hreal := real_of_make hown hxq (hown.2.2.1 ℓ0 x _ _ hacc)
  have hinit := zz_initBal x hxq
  refine ⟨fun b hb hlt w hw => ?_, fun _ w hw => ?_⟩
  · rcases Int.lt_trichotomy (zz b) (zz (reps.foldl maxStep (W32 (-1)))) with h | h | h
    · exact (hsafe.1 ℓ0 x _ _ hacc).1 b hb h w hw
    · have hb' : b = reps.foldl maxStep (W32 (-1)) := zz_inj h
      subst hb'
      refine blocked_reps hrr hA hR hlt (fun e' he' hv' => ?_)
      obtain ⟨ℓ1, hacc1⟩ := hvf.2 _ x _ w hv'
      exact hw (hop.2.1 ℓ1 ℓ0 x _ w _ hacc1 hacc)
    · exact blocked_above hrr hhi hA hR hlt h w
  · rcases hreal with h | h
    · rw [h] at hacc; exact hA.accInit ℓ0 x _ hacc w
    · refine (hsafe.1 ℓ0 x _ _ hacc).2 ?_ w hw
      simp [nR] at hxq h; omega

theorem safe_sub3 {e : PReply} (he : e ∈ reps)
    (hnc : ∀ e ∈ reps, stGe e.m.status stCOMMITTED = false)
    (hna : ∀ e ∈ reps, ¬ (e.m.vballot = reps.foldl maxStep (W32 (-1)) ∧ e.m.status = stACCEPTED))
    (hi : isInitialBallot (reps.foldl maxStep (W32 (-1))) (W32 x.q) = true)
    (hok : subCase3Ok reps (reps.foldl maxStep (W32 (-1))) e = true) :
    S.safeAcc x n ⟨e.m.command, e.m.seq, e.m.deps⟩ := by
  obtain ⟨hwf, -, -, -, -, hown, hop, hvf, hrr, hhi, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsafe, -⟩ := hI
  have hinit := zz_initBal x hxq
  have hmx : reps.foldl maxStep (W32 (-1)) = initBal x := by
    simpa [isInitialBallot, initBal] using hi
  have hmn : zz (reps.foldl maxStep (W32 (-1))) < zz n := by
    rw [hmx, hinit]; simp [nR] at hxq hn; omega
  refine ⟨fun b hb hlt w hw => ?_, fun _ w hw => ?_⟩
  · rcases Int.lt_trichotomy (zz b) (zz (reps.foldl maxStep (W32 (-1)))) with h | h | h
    · obtain ⟨-, h2⟩ := zz_real hxq hb
      rw [hmx] at h
      have := h2 (Int.le_of_lt h); rw [this] at h; exact absurd h (Int.lt_irrefl _)
    · have hb' : b = reps.foldl maxStep (W32 (-1)) := zz_inj h
      subst hb'
      exact blocked_at_max hrr hhi hA hR hmn hnc hna w
    · exact blocked_above hrr hhi hA hR hlt h w
  · -- two non-leader reporters pre-accepted the chosen value at the initial ballot
    left
    rw [hmx] at hok
    obtain ⟨R, hRdef⟩ : ∃ R, R = reps.filter (fun o => isPreAcceptedAt (initBal x) o &&
      o.m.acceptorId != o.m.replica && o.m.seq == e.m.seq && depsEqual o.m.deps e.m.deps) :=
      ⟨_, rfl⟩
    have hok' := hok
    simp only [subCase3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨⟨hpe, -⟩, hlen⟩ := hok'
    rw [← hRdef] at hlen
    obtain ⟨hane, -, hrepe, hxe, Ee, hEe⟩ := hR.mem e he
    have hpaE : isPA e.m.status := by
      simp only [isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpe
      exact hpe.2
    have hvbe : e.m.vballot = initBal x := by
      simp only [isPreAcceptedAt, Bool.and_eq_true, beq_iff_eq] at hpe; exact hpe.1
    have hve := rep_reported hrr hxe hEe (Or.inl hpaE)
    rw [hvbe] at hve
    obtain ⟨ℓe, v0e, hphe, hce⟩ := hvf.1 _ x _ _ _ hve hpaE
    refine ⟨R.map (fun o => toN o.m.acceptorId), reps_nodup hrr hR (hRdef ▸ List.filter_sublist), ?_,
      fun a ha => ?_⟩
    · simp only [List.length_map]; exact hlen
    · simp only [List.mem_map] at ha
      obtain ⟨o, ho, rfl⟩ := ha
      rw [hRdef, List.mem_filter] at ho
      obtain ⟨hor, hp⟩ := ho
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
      obtain ⟨⟨⟨hpo, hneq⟩, hseq⟩, hdeq⟩ := hp
      obtain ⟨hano, hno, hrepo, hxo, Eo, hEo⟩ := hR.mem o hor
      have hpaO : isPA o.m.status := by
        simp only [isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpo
        exact hpo.2
      have hvbo : o.m.vballot = initBal x := by
        simp only [isPreAcceptedAt, Bool.and_eq_true, beq_iff_eq] at hpo; exact hpo.1
      refine ⟨hano, fun h => hneq ?_, fun st hst hv => hw ?_, Or.inl ?_⟩
      · rw [acc_eq hrr hEo, hrepo, h]
      · have hvo := rep_reported hrr hxo hEo (Or.inl hpaO)
        rw [hvbo] at hvo
        have h1 := hA.pa _ x _ _ _ _ _ hst hpaO hv hvo
        obtain ⟨ℓo, v0o, hpho, hco⟩ := hvf.1 _ x _ _ _ hvo hpaO
        have h2 := (hop.1 ℓo ℓe x _ v0o v0e hpho hphe).2.1
        have hdl : o.m.deps.length = e.m.deps.length := by
          rw [hA.deps _ o.m Eo hEo (fun h => by rw [h] at hpaO; revert hpaO; unfold isPA; decide),
            hA.deps _ e.m Ee hEe (fun h => by rw [h] at hpaE; revert hpaE; unfold isPA; decide)]
        rw [h1]
        simp only [Val.mk.injEq]
        refine ⟨?_, hseq, depsEqual_eq hdl hdeq⟩
        simp only at hco hce; rw [hco, hce, h2]
      · obtain ⟨wa, hwa, hle⟩ := hA.bal _ o.m Eo hano hEo
        rw [hxo, hno] at *
        exact ⟨wa, hwa, Or.inl (by rw [hinit]; simp [nR] at hxq hn; omega)⟩

/-- No reporter other than the leader: the non-leader reporters, at least two. -/
theorem nonleaders (hrr : Inv.repliesReportVotes S) :
    ((reps.map (fun e => toN e.m.acceptorId)).filter (· ≠ x.q)).Nodup ∧
    2 ≤ ((reps.map (fun e => toN e.m.acceptorId)).filter (· ≠ x.q)).length := by
  have hnd := reps_nodup hrr hR (List.Sublist.refl _)
  refine ⟨List.filter_sublist.nodup hnd, ?_⟩
  have hsp := List.subperm_of_subset hnd (l₂ := x.q :: (reps.map (fun e => toN e.m.acceptorId)).filter (· ≠ x.q))
    (fun a ha => by
      by_cases h : a = x.q
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨ha, by simpa using h⟩))
  have h1 := hsp.length_le
  have h3 := hR.len
  simp only [List.length_map, List.length_cons] at h1
  simp only [nR] at h3
  omega

theorem safe_sub56 (hnov : ∀ r st u, isPA st → ¬ S.ev r (.vote x n st u)) (lr : Bool)
    (hlr : lr = true → ∃ e ∈ reps, toN e.m.acceptorId = x.q)
    (hlr' : lr = false → ∀ e ∈ reps, e.m.acceptorId ≠ e.m.replica)
    (hnc : ∀ e ∈ reps, stGe e.m.status stCOMMITTED = false)
    (hna : ∀ e ∈ reps, ¬ (e.m.vballot = reps.foldl maxStep (W32 (-1)) ∧ e.m.status = stACCEPTED))
    (h3f : isInitialBallot (reps.foldl maxStep (W32 (-1))) (W32 x.q) = true → lr = false →
      ∀ e ∈ reps, subCase3Ok reps (reps.foldl maxStep (W32 (-1))) e = false) :
    S.safePh x n := by
  have hI' := hI
  obtain ⟨hwf, -, -, -, -, hown, hop, hvf, hrr, hhi, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsafe, -⟩ := hI'
  have hinit := zz_initBal x hxq
  have hin : zz (initBal x) < zz n := by rw [hinit]; simp [nR] at hxq hn; omega
  have hfm := foldl_max reps (W32 (-1))
  -- the highest report is NONE (`-1`) or pre-accepted
  have hcase : zz (reps.foldl maxStep (W32 (-1))) = -1 ∨
      ∃ e0 ∈ reps, e0.m.vballot = reps.foldl maxStep (W32 (-1)) ∧ isPA e0.m.status := by
    rcases hfm.2.2 with h | ⟨e0, he0, h⟩
    · left; rw [h]; decide
    · obtain ⟨-, -, -, -, E0, hE0⟩ := hR.mem e0 he0
      rcases hA.status _ e0.m E0 hE0 with hs | hs | hs | hs
      · left; rw [← h]; exact hA.none _ e0.m E0 hE0 hs
      · exact Or.inr ⟨e0, he0, h, hs⟩
      · exact absurd ⟨h, hs⟩ (hna e0 he0)
      · exact absurd (stGe_of_committed hs) (by rw [hnc e0 he0]; simp)
  -- reporters whose votes are all below `n` are at most `maxVbal`
  have hbal : ∀ e ∈ reps, ∃ wa, (S.rep (toN e.m.acceptorId)).inst x = some wa ∧
      zz (initBal x) < zz wa.bal := by
    intro e he
    obtain ⟨han, hne, -, hxe, E, hE⟩ := hR.mem e he
    obtain ⟨wa, hwa, hle⟩ := hA.bal _ e.m E han hE
    rw [hxe, hne] at *
    exact ⟨wa, hwa, by omega⟩
  rcases hcase with hm1 | ⟨e0, he0, hv0, hpa0⟩
  · -- every report is NONE: the reporters voted nothing below `n`
    refine ⟨fun b hb hlt w => blocked_above hrr hhi hA hR hlt ?_ w, fun _ w => Or.inl ?_⟩
    · have := (zz_real hxq hb).1; omega
    · obtain ⟨hnd, hlen⟩ := nonleaders hI hA hxq hn hR hrr
      refine ⟨_, hnd, hlen, fun a ha => ?_⟩
      simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at ha
      obtain ⟨⟨e, he, rfl⟩, hq⟩ := ha
      obtain ⟨han, hne, -, hxe, E, hE⟩ := hR.mem e he
      refine ⟨han, hq, fun st hst hv => ?_, Or.inl ((hbal e he).imp fun wa h => ⟨h.1, Or.inl h.2⟩)⟩
      have := (rep_vote hrr hhi hne hxe hE hv hin).2
      have := hfm.2.1 e he
      rw [hinit] at *; omega
  · -- the highest report is a pre-accept vote: the Phase 1 at `maxVbal` was safe
    obtain ⟨-, hne0, -, hxe0, E0, hE0⟩ := hR.mem e0 he0
    have hv := rep_reported hrr hxe0 hE0 (Or.inl hpa0)
    rw [hv0] at hv
    obtain ⟨ℓ0, v0, hph, -⟩ := hvf.1 _ x _ _ _ hv hpa0
    have hreal : realBal x (reps.foldl maxStep (W32 (-1))) := by
      obtain ⟨p, p', -, hp, -⟩ := hown.2.1 ℓ0 x _ v0 hph
      exact real_of_make hown hxq (List.mem_of_getElem? hp)
    have hIH := hsafe.2 ℓ0 x _ v0 hph
    have hmn : zz (reps.foldl maxStep (W32 (-1))) < zz n := by
      have h1 := hA.vbal _ e0.m E0 hE0
      rw [hne0, hv0] at h1
      rcases Int.lt_or_eq_of_le h1 with h | h
      · exact h
      · rw [zz_inj h] at hv; exact absurd hv (hnov _ _ _ hpa0)
    refine ⟨fun b hb hlt w => ?_, fun _ w => ?_⟩
    · rcases Int.lt_trichotomy (zz b) (zz (reps.foldl maxStep (W32 (-1)))) with h | h | h
      · exact hIH.1 b hb h w
      · have hb' : b = reps.foldl maxStep (W32 (-1)) := zz_inj h
        subst hb'
        exact blocked_at_max hrr hhi hA hR hmn hnc hna w
      · exact blocked_above hrr hhi hA hR hlt h w
    · by_cases hlt : zz (initBal x) < zz (reps.foldl maxStep (W32 (-1)))
      · exact hIH.2 hlt w
      · have hmx : reps.foldl maxStep (W32 (-1)) = initBal x :=
          (zz_real hxq hreal).2 (Int.not_lt.mp hlt)
        cases lr with
        | true =>
          -- the leader reported: it promised above the initial ballot and never fast-committed
          obtain ⟨eL, heL, hL⟩ := hlr rfl
          obtain ⟨-, -, -, hxL, EL, hEL⟩ := hR.mem eL heL
          obtain ⟨wl, hwl, hlt'⟩ := hbal eL heL
          rw [hL] at hwl hEL
          refine Or.inr ⟨⟨wl, hwl, hlt'⟩, fun hf => ?_⟩
          have := hA.fast x w eL.m EL hf hEL hxL
          exact absurd (stGe_of_committed this) (by rw [hnc eL heL]; simp)
        | false =>
          -- no reporter is the leader; at most one of them pre-accepted `w` (two would make
          -- sub-case 3 apply)
          left
          classical
          have hw : ∀ o ∈ reps, (∃ st, isPA st ∧ S.ev (toN o.m.acceptorId)
              (.vote x (initBal x) st w)) →
              o.m.vballot = initBal x ∧ isPA o.m.status ∧ w = ⟨o.m.command, o.m.seq, o.m.deps⟩ := by
            rintro o ho ⟨st, hst, hv⟩
            obtain ⟨han, hno, hrepo, hxo, Eo, hEo⟩ := hR.mem o ho
            obtain ⟨-, hle⟩ := rep_vote hrr hhi hno hxo hEo hv hin
            have hge := hfm.2.1 o ho
            rw [hmx] at hge
            have hvb : o.m.vballot = initBal x := zz_inj (by omega)
            rcases hA.status _ o.m Eo hEo with hs | hs | hs | hs
            · have := hA.none _ o.m Eo hEo hs; rw [hvb, hinit] at this; omega
            · refine ⟨hvb, hs, ?_⟩
              have hvo := rep_reported hrr hxo hEo (Or.inl hs)
              rw [hvb] at hvo
              exact hA.pa _ x _ _ _ _ _ hst hs hv hvo
            · exact absurd ⟨hvb.trans hmx.symm, hs⟩ (hna o ho)
            · exact absurd (stGe_of_committed hs) (by rw [hnc o ho]; simp)
          have hpre : ∀ o ∈ reps, (∃ st, isPA st ∧ S.ev (toN o.m.acceptorId)
              (.vote x (initBal x) st w)) →
              isPreAcceptedAt (reps.foldl maxStep (W32 (-1))) o = true := by
            intro o ho hp
            obtain ⟨h1, h2, -⟩ := hw o ho hp
            simp only [isPreAcceptedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
            exact ⟨by rw [h1, hmx], h2⟩
          have hle1 : (reps.filter (fun o => decide (∃ st, isPA st ∧ S.ev (toN o.m.acceptorId)
              (.vote x (initBal x) st w)))).length ≤ 1 := by
            refine Classical.byContradiction fun hc => ?_
            have hnd : reps.Nodup := nodup_of_map _ hR.nodup
            generalize hF : reps.filter (fun o => decide (∃ st, isPA st ∧
              S.ev (toN o.m.acceptorId) (.vote x (initBal x) st w))) = F at hc
            match F, hF, hc with
            | [], _, hc => simp at hc
            | [_], _, hc => simp at hc
            | o1 :: o2 :: _, hF, _ =>
              have hm1 : o1 ∈ reps.filter _ := hF ▸ List.mem_cons_self
              have hm2 : o2 ∈ reps.filter _ := hF ▸ List.mem_cons_of_mem _ List.mem_cons_self
              have hnd' := hF ▸ (List.filter_sublist.nodup hnd)
              have h12 : o1 ≠ o2 := by
                intro h; subst h; simp at hnd'
              rw [List.mem_filter, decide_eq_true_eq] at hm1 hm2
              obtain ⟨-, -, hw1⟩ := hw o1 hm1.1 hm1.2
              obtain ⟨-, -, hw2⟩ := hw o2 hm2.1 hm2.2
              have hok : subCase3Ok reps (reps.foldl maxStep (W32 (-1))) o1 = true := by
                have hc1 : ∀ o ∈ [o1, o2], o ∈ reps.filter (fun o => isPreAcceptedAt
                    (reps.foldl maxStep (W32 (-1))) o && o.m.acceptorId != o.m.replica &&
                    o.m.seq == o1.m.seq && depsEqual o.m.deps o1.m.deps) := by
                  intro o ho
                  have ho' : o ∈ reps ∧ w = ⟨o.m.command, o.m.seq, o.m.deps⟩ := by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
                    rcases ho with rfl | rfl
                    · exact ⟨hm1.1, hw1⟩
                    · exact ⟨hm2.1, hw2⟩
                  have hoe : (⟨o.m.command, o.m.seq, o.m.deps⟩ : Val) =
                      ⟨o1.m.command, o1.m.seq, o1.m.deps⟩ := ho'.2.symm.trans hw1
                  simp only [Val.mk.injEq] at hoe
                  rw [List.mem_filter]
                  refine ⟨ho'.1, ?_⟩
                  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
                  refine ⟨⟨⟨hpre o ho'.1 ?_, hlr' rfl o ho'.1⟩, hoe.2.1⟩, by
                    rw [hoe.2.2]; exact depsEqual_self _⟩
                  rcases ho' with ⟨h1, h2⟩
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
                  rcases ho with rfl | rfl
                  · exact hm1.2
                  · exact hm2.2
                simp only [subCase3Ok, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
                refine ⟨⟨hpre o1 hm1.1 hm1.2, hlr' rfl o1 hm1.1⟩, ?_⟩
                exact two_le_of_mem (hc1 o1 (by simp)) (hc1 o2 (by simp)) h12
              have := h3f (by simp [isInitialBallot, hmx, initBal]) rfl o1 hm1.1
              rw [hok] at this; cases this
          have hlen := filter_len reps (fun o => decide (∃ st, isPA st ∧ S.ev (toN o.m.acceptorId)
              (.vote x (initBal x) st w)))
          refine ⟨(reps.filter (fun o => ¬ decide (∃ st, isPA st ∧ S.ev (toN o.m.acceptorId)
              (.vote x (initBal x) st w)))).map (fun e => toN e.m.acceptorId),
            reps_nodup hrr hR List.filter_sublist, ?_, fun a ha => ?_⟩
          · simp only [List.length_map]; have := hR.len; simp only [nR] at this; omega
          · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at ha
            obtain ⟨o, ⟨ho, hnp⟩, rfl⟩ := ha
            obtain ⟨han, hno, hrepo, hxo, Eo, hEo⟩ := hR.mem o ho
            refine ⟨han, fun h => hlr' rfl o ho ?_, fun st hst hv => hnp ⟨st, hst, hv⟩,
              Or.inl ((hbal o ho).imp fun wa h => ⟨h.1, Or.inl h.2⟩)⟩
            rw [acc_eq hrr hEo, hrepo, h]

/-- **The recovery's decision is safe** (sub-cases 2/3: the Accept of the chosen reply's value;
sub-cases 5/6: the Phase 1). -/
theorem decide_safe (hnov : ∀ r st u, isPA st → ¬ S.ev r (.vote x n st u)) (lr : Bool)
    (hlr : lr = true → ∃ e ∈ reps, toN e.m.acceptorId = x.q)
    (hlr' : lr = false → ∀ e ∈ reps, e.m.acceptorId ≠ e.m.replica) :
    ((prepDecide reps (reps.foldl maxStep (W32 (-1))) lr (W32 x.q)).1 = 2 ∨
      (prepDecide reps (reps.foldl maxStep (W32 (-1))) lr (W32 x.q)).1 = 3 →
      ∀ e, (prepDecide reps (reps.foldl maxStep (W32 (-1))) lr (W32 x.q)).2 = some e →
        S.safeAcc x n ⟨e.m.command, e.m.seq, e.m.deps⟩) ∧
    ((prepDecide reps (reps.foldl maxStep (W32 (-1))) lr (W32 x.q)).1 ≠ 1 →
      (prepDecide reps (reps.foldl maxStep (W32 (-1))) lr (W32 x.q)).1 ≠ 2 →
      (prepDecide reps (reps.foldl maxStep (W32 (-1))) lr (W32 x.q)).1 ≠ 3 → S.safePh x n) := by
  rcases prepDecide_cases reps (reps.foldl maxStep (W32 (-1))) lr (W32 x.q) with
    h1 | ⟨hnc, ⟨h2, e, hde, he, hev, hes⟩ | ⟨hna, ⟨h3, hi, hlf, e, hde, he, hok⟩ | ⟨n1, n2, n3, h3f⟩⟩⟩
  · exact ⟨fun h => by omega, fun h => absurd h1 h⟩
  · refine ⟨fun _ e' he' => ?_, fun _ h => absurd h2 h⟩
    rw [hde] at he'; cases he'
    exact safe_sub2 hI hA hxq hn hR he hev hes
  · refine ⟨fun _ e' he' => ?_, fun _ _ h => absurd h3 h⟩
    rw [hde] at he'; cases he'
    exact safe_sub3 hI hA hxq hn hR he hnc hna hi hok
  · exact ⟨fun h => by omega, fun _ _ _ =>
      safe_sub56 hI hA hxq hn hR hnov lr hlr hlr' hnc hna h3f⟩

end

end

end DecideProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
