/-
A handler step of replica `i` that commits its instance `x` with a value `v` that is already
decided (`S.committedVal x v`): the record becomes COMMITTED with `v` at ballot `b` (at least its
`bal` and its bookkeeping's `lastTriedBallot`), the bookkeeping becomes a COMMITTED, non-preparing
one with the same ballot and counters, the event `commit x b v` is logged, and nothing is sent
(`inv_commit_known`). Used by `handlePrepareReply`'s sub-case 1.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HLocal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecHS
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.PMHS

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace RecCommitProof

open HStepProof HLocal SafeProof AuxProof

/-- `slotsOn` reads only the records of its instances. -/
theorem slotsOn_congr (σ1 σ2 : RState) (xs : List InstId) (k : w64)
    (h : ∀ y ∈ xs, σ1.inst y = σ2.inst y) : Sys.slotsOn σ1 xs k = Sys.slotsOn σ2 xs k := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [Sys.slotsOn, List.flatMap_cons] at ih ⊢
    rw [h y (by simp), ih (fun z hz => h z (by simp [hz]))]

/-- The bookkeeping after a commit with a known value. -/
def LbCommitted (lb lb' : LbRec) (v : Val) : Prop :=
  lb'.lastTriedBallot = lb.lastTriedBallot ∧ zz lb'.ballot ≤ zz lb.lastTriedBallot ∧
  lb'.status = stCOMMITTED ∧ lb'.preparing = false ∧ lb'.tryingToPreAccept = false ∧
  lb'.clientProposals = lb.clientProposals ∧ lb'.preAcceptOKs = lb.preAcceptOKs ∧
  lb'.acceptOKs = lb.acceptOKs ∧ depsOk lb'.deps ∧ lb'.cmds = some v.cmds

/-- The committed record. -/
def comKnown (w : InstRec) (lb' : LbRec) (b : w32) (v : Val) : InstRec :=
  { w with cmds := some v.cmds, bal := b, vbal := b, seq := v.seq, deps := v.deps,
           status := stCOMMITTED, lb := some lb' }

/-- **A commit of an already decided value keeps the invariant.** -/
theorem inv_commit_known (S S' : Sys) (i : Nat) (σ' : RState) (x : InstId) (w : InstRec)
    (lb lb' : LbRec) (b : w32) (v : Val) (hS : Inv S) (hi : i < nR) (hidle : S.idle i)
    (hH : HS S S' i σ' [.commit x b v] (fun _ => []) none)
    (hchan : S'.proposeChan = S.proposeChan)
    (hσ : σ'.inst = upd (S.rep i).inst x (some (comKnown w lb' b v)))
    (hc : σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (S.rep i).crtInstance ∧ σ'.conflicts = (S.rep i).conflicts ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store)
    (hcls : σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut)
    (hw : (S.rep i).inst x = some w) (hlb : w.lb = some lb) (hnc : ¬ isCommitted w.status)
    (hb : zz w.bal ≤ zz b) (hlt : zz lb.lastTriedBallot ≤ zz b) (hb0 : 0 ≤ zz b)
    (hcv : S.committedVal x v) (hdeps : depsOk v.deps) (hcne : v.cmds ≠ [])
    (hk : LbCommitted lb lb' v) (hlI : zz (initBal x) < zz lb.lastTriedBallot) : Inv S' := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ := hk
  generalize hw'd : comKnown w lb' b v = w' at hσ
  have hA := hS.2
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27⟩ := hS.1
  -- events
  have hE : ∀ r e, S'.ev r e ↔ S.ev r e ∨ (r = i ∧ e = .commit x b v) := by
    intro r e; rw [hH.ev_iff]; simp
  have hold : ∀ r e, S'.ev r e → (∀ y b' v', e ≠ .commit y b' v') → S.ev r e := by
    intro r e he hne
    rcases (hE r e).mp he with h | ⟨-, rfl⟩
    · exact h
    · exact absurd rfl (hne x b v)
  have hnotE : ∀ e, (∀ y b' v', e ≠ .commit y b' v') → i = i → e ∉ [Event.commit x b v] := by
    intro e hne _ h; simp only [List.mem_singleton] at h; exact hne x b v h
  have hmsgs : ∀ fr to m, m ∈ S'.msgs fr to ↔ m ∈ S.msgs fr to := by
    intro fr to m; rw [hH.mem_msgs]; simp [intendedOf]
  have hcv' : ∀ y u, S'.committedVal y u ↔ S.committedVal y u := by
    intro y u
    constructor
    · rintro (⟨r, b', h⟩ | ⟨fr, to, m, hm, hy, rfl⟩)
      · rcases (hE r _).mp h with h | ⟨-, h⟩
        · exact Or.inl ⟨r, b', h⟩
        · simp only [Event.commit.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h; exact hcv
      · exact Or.inr ⟨fr, to, m, (hmsgs _ _ _).mp hm, hy, rfl⟩
    · rintro (⟨r, b', h⟩ | ⟨fr, to, m, hm, hy, rfl⟩)
      · exact Or.inl ⟨r, b', hH.ev_old h⟩
      · exact Or.inr ⟨fr, to, m, hH.msgs_old hm, hy, rfl⟩
  have hprepR : ∀ r m e, S'.prepReport r m e ↔ S.prepReport r m e := by
    intro r m e
    constructor
    · rintro ⟨he, ⟨to, hm, rfl⟩ | rfl⟩
      · exact ⟨hold r _ he (fun _ _ _ h => by cases h), Or.inl ⟨to, (hmsgs _ _ _).mp hm, rfl⟩⟩
      · exact ⟨hold r _ he (fun _ _ _ h => by cases h), Or.inr rfl⟩
    · rintro ⟨he, ⟨to, hm, rfl⟩ | rfl⟩
      · exact ⟨hH.ev_old he, Or.inl ⟨to, hH.msgs_old hm, rfl⟩⟩
      · exact ⟨hH.ev_old he, Or.inr rfl⟩
  have hvote : ∀ r y b' st u, S'.ev r (.vote y b' st u) → S.ev r (.vote y b' st u) :=
    fun r y b' st u h => hold r _ h (fun _ _ _ h => by cases h)
  have hevB : ∀ r e r' e', S'.evBefore r e r' e' → S.ev r' e' →
      (∀ y b' v', e' ≠ .commit y b' v') → S.evBefore r e r' e' :=
    fun r e r' e' h h' hne => hH.evBefore_back h h' (fun _ => hnotE e' hne rfl)
  have hcnt : ∀ fr to p, S'.cnt fr to p = S.cnt fr to p := by
    intro fr to p; rw [hH.cnt_eq]; split <;> simp [intendedOf]
  have hall : ∀ fr to p, S.allDeliv fr to p → S'.allDeliv fr to p :=
    fun fr to p h => hH.allDeliv_old h (fun _ m hm => by simp [intendedOf] at hm)
  -- records
  have hrep : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some w' else (S.rep r).inst y := by
    intro r y
    rw [hH.rep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same, hσ, upd_apply, true_and]
    · simp [upd_other _ _ _ _ hr, hr]
  have R1 : ∀ r y w2, (S'.rep r).inst y = some w2 →
      (i = r ∧ x = y ∧ w' = w2) ∨ ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
    intro r y w2 h; rw [hrep] at h; split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; simp only [Option.some.injEq] at h
      exact Or.inl ⟨rfl, rfl, h⟩
    · rename_i hc; exact Or.inr ⟨h, hc⟩
  have R2 : ∀ r y w1, (S.rep r).inst y = some w1 →
      (i = r ∧ x = y ∧ w = w1) ∨ (S'.rep r).inst y = some w1 := by
    intro r y w1 h
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [hw] at h; cases h; exact Or.inl ⟨rfl, rfl, rfl⟩
    · right; rw [hrep, if_neg hc]; exact h
  have R3 : (S'.rep i).inst x = some w' := by rw [hrep]; simp
  have hfl : ∀ r, (S'.rep r).id = (S.rep r).id ∧ (S'.rep r).peerOrder = (S.rep r).peerOrder ∧
      (S'.rep r).crtInstance = (S.rep r).crtInstance ∧
      (S'.rep r).conflicts = (S.rep r).conflicts ∧
      (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store := by
    intro r
    by_cases hr : r = i
    · subst hr; rw [hH.rep_self]; exact ⟨c1, c2, c3, c4, c5, c6⟩
    · rw [hH.rep_other hr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the new record
  have W : w'.cmds = some v.cmds ∧ w'.bal = b ∧ w'.vbal = b ∧ w'.status = stCOMMITTED ∧
      w'.seq = v.seq ∧ w'.deps = v.deps ∧ w'.lb = some lb' ∧ w'.id = w.id ∧
      instVal w' = v := by
    rw [← hw'd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [instVal, comKnown]⟩
  obtain ⟨W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ := W
  have hcom' : isCommitted w'.status := Or.inl W4
  have hwnex : w.status ≠ stEXECUTED := fun h => hnc (Or.inr h)
  have hw'nex : w'.status ≠ stEXECUTED := by rw [W4]; decide
  have hex : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
    intro r y
    constructor
    · rintro ⟨w2, h2, hs⟩
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hw'nex
      · exact ⟨w2, h, hs⟩
    · rintro ⟨w1, h1, hs⟩
      rcases R2 r y w1 h1 with ⟨-, -, rfl⟩ | h
      · exact absurd hs hwnex
      · exact ⟨w1, h, hs⟩
  have hxlog : x ∉ S.execLog i := by
    intro h
    obtain ⟨w1, h1, hs⟩ := ((s18 i hi).2.1 x).mp h
    rw [hw] at h1; cases h1; exact hwnex hs
  have hwb := s5.1 i hi x w hw
  have hsafeM : SafeMono S S' := by
    refine ⟨fun r y w1 h1 => ?_, fun r e h => hH.ev_old h,
      fun r y b' st u h => Or.inl (hvote r y b' st u h),
      fun y u h => Or.inl (hold _ _ h (fun _ _ _ h => by cases h)),
      fun a y m h _ _ => Or.inl ((hmsgs _ _ _).mp h)⟩
    rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
    · exact ⟨w', R3, by rw [W2]; exact hb, fun _ => Or.inl (by rw [W4]; decide)⟩
    · exact ⟨w1, h, Int.le_refl _, fun h => Or.inl h⟩
  have hsafe : Inv.safe S' := safe_frame hsafeM s26
    (fun r y b' v' h => hold r _ h (fun _ _ _ h => by cases h))
    (fun r y b' v' h => hold r _ h (fun _ _ _ h => by cases h))
  have hwf : Inv.wf S' := by
    obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := s1
    refine ⟨fun r hr => by rw [(hfl r).1]; exact w1' r hr, fun r hr y w2 h2 => ?_,
      fun r hr q hq => by rw [(hfl r).2.2.1]; exact w3' r hr q hq,
      fun r hr q k p hk => ?_, fun r hr q hq n' hn' => ?_, fun fr' to hne => ?_,
      fun fr' to n' hn' => ?_, fun r b' hb' => ?_⟩
    · rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · obtain ⟨g1, g2, g3, -, -, g6, g7⟩ := w2' i hi x w hw
        refine ⟨by rw [W8]; exact g1, g2, g3, fun _ => by rw [W6]; exact hdeps,
          fun lb2 hl2 _ => ?_, fun hq => by rw [W7]; simp, fun lb2 ps hl2 hps => ?_⟩
        · rw [W7] at hl2; cases hl2; exact k9
        · rw [W7] at hl2; cases hl2; rw [hH.owner]; rw [k6] at hps; exact g7 lb ps hlb hps
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2' r hr y w2 h
        exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
    · rw [(hfl r).2.2.2.1] at hk
      obtain ⟨k1', k2', k3'⟩ := w4' r hr q k p hk
      have grow : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
        intro y hy hy'
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h
        · rw [R3] at hy'; cases hy'
        · rw [h] at hy'; cases hy'
      exact ⟨k1', fun h0 => grow _ (k2' h0), fun h0 => grow _ (k3' h0)⟩
    · rw [(hfl r).2.2.2.2.1] at hn'
      exact (hex r _).mpr (w5' r hr q hq n' hn')
    · exact w6' fr' to (fun h => hne (by
        apply List.eq_nil_iff_forall_not_mem.mpr; intro m hm; rw [hmsgs] at hm; rw [h] at hm
        cases hm))
    · rcases hH.delOk fr' to n' hn' with h | h
      · rw [hH.sent]; exact w7' fr' to n' h
      · rw [hH.sent]; exact h
    · rw [hH.pending] at hb'
      by_cases hr : r = i
      · subst hr; simp at hb'
      · rw [upd_other _ _ _ _ hr] at hb'
        obtain ⟨d1, d2, d3, d4, d5, d6, w1, lb1, h1, hl1⟩ := w8' r b' hb'
        refine ⟨d1, by rw [hH.execCur]; exact d2, d3, d4, d5, d6, w1, lb1, ?_, hl1⟩
        rw [hrep, if_neg (fun h => hr h.1)]; exact h1
  have hbal : Inv.ballots S' := by
    refine ⟨fun r hr y w2 h2 => ?_, fun r hr y b' st u he => ?_⟩
    · rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W2, W3]; exact Int.le_refl _
      · exact s5.1 r hr y w2 h
    · obtain ⟨w1, h1, hle⟩ := s5.2 r hr y b' st u (hvote _ _ _ _ _ he)
      rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · exact ⟨w', R3, by rw [W2]; omega⟩
      · exact ⟨w1, h, hle⟩
  have hlbI : Inv.lbInv S' := by
    intro r hr y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, hne⟩
    · rw [W7] at hl2; cases hl2
      obtain ⟨a1, a2, a3, a4, -, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, -, -⟩ :=
        s11 i hi x w lb hw hlb
      refine ⟨by rw [k1]; exact hH.ev_old a1, by rw [k1]; exact k2, k5,
        fun b' u hv0 => by
          rw [k1]; exact a4 b' u (hv0.imp (fun h => hold _ _ h (fun _ _ _ h => by cases h))
            (fun h => hold _ _ h (fun _ _ _ h => by cases h))),
        fun c1 => (by rw [k3] at c1; rcases c1 with h | h <;> cases h),
        ⟨Q, q1, (by rw [k7]; exact q2), fun a m' hq => ?_⟩,
        ⟨Q', q1', (by rw [k8]; exact q2'), fun a hq => ?_⟩,
        fun c1 => (by rw [k3] at c1; cases c1), fun c1 => (by rw [k4] at c1; cases c1)⟩
      · obtain ⟨b1, b2, b3, b4, b5, -⟩ := q3 a m' hq
        exact ⟨b1, b2, hH.deliveredMsg_old b3, b4, by rw [k1]; exact b5,
          fun c1 => (by rw [k3] at c1; rcases c1 with h | h <;> cases h)⟩
      · obtain ⟨b1, b2, m', b3, b4, b5⟩ := q3' a hq
        exact ⟨b1, b2, m', hH.deliveredMsg_old b3, b4, by rw [k1]; exact b5⟩
    · obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
        s11 r hr y w2 lb2 h hl2
      refine ⟨hH.ev_old a1, a2, a3,
        fun b' u hv0 => a4 b' u (hv0.imp (fun h => hold _ _ h (fun _ _ _ h => by cases h))
            (fun h => hold _ _ h (fun _ _ _ h => by cases h))),
        fun c1 c2 => ?_, ⟨Q, q1, q2, fun a m' hq => ?_⟩, ⟨Q', q1', q2', fun a hq => ?_⟩,
        fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
      · obtain ⟨d1, d2, u, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, u, hH.ev_old d3, d4⟩
      · obtain ⟨b1, b2, b3, b4⟩ := q3 a m' hq; exact ⟨b1, b2, hH.deliveredMsg_old b3, b4⟩
      · obtain ⟨b1, b2, m', b3, b4⟩ := q3' a hq; exact ⟨b1, b2, m', hH.deliveredMsg_old b3, b4⟩
      · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
      · obtain ⟨c1, c2⟩ := a9 hp
        refine ⟨c1, fun e he' => ?_⟩
        obtain ⟨d1, d2, d3⟩ := c2 e he'
        refine ⟨d1, d2, ?_⟩
        rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e1, hH.deliveredMsg_old e2⟩
        · exact Or.inr ⟨e1, hH.ev_old e2⟩
  have hagr : Inv.agreement S' := by
    refine ⟨fun y u u' h1 h2 => s12.1 y u u' ((hcv' _ _).mp h1) ((hcv' _ _).mp h2),
      fun r hr y w2 h2 hc' => ?_⟩
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
    · exact ⟨by rw [W1]; simp, (hcv' _ _).mpr (by rw [W9]; exact hcv)⟩
    · obtain ⟨d1, d2⟩ := s12.2 r hr y w2 h hc'
      exact ⟨d1, (hcv' _ _).mpr d2⟩
  have hdE : S'.dEdge = S.dEdge := by
    funext y z; simp only [Sys.dEdge, hcv']
  have hsO : S'.sccOrd = S.sccOrd := by
    funext y z; simp only [Sys.sccOrd, hcv']
  have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
    intro r k
    have hcur : S'.curSlots r k = S.curSlots r k := by
      by_cases hr : r = i
      · subst hr; simp only [Sys.curSlots, hH.execCur, hidle.2]
      · simp only [Sys.curSlots, hH.execCur, hH.execIdx, hH.rep_other hr]
    simp only [Sys.lexec, hcur, hH.execLog]
    congr 1
    by_cases hr : r = i
    · subst hr
      refine slotsOn_congr _ _ _ _ (fun y hy => ?_)
      rw [hrep, if_neg]; rintro ⟨-, rfl⟩; exact hxlog hy
    · rw [hH.rep_other hr]
  have hexec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧
      Inv.execPrefix S' := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
    · obtain ⟨e1, e2, e3⟩ := s18 r hr
      refine ⟨by rw [hH.execLog]; exact e1, fun y => by rw [hH.execLog, hex]; exact e2 y,
        fun y w2 h2 hs => ?_⟩
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, hne⟩
      · exact absurd hs hw'nex
      obtain ⟨d1, d2⟩ := e3 y w2 h hs
      refine ⟨(hcv' _ _).mpr d1, fun z hz => ?_⟩
      rw [hex, hH.execCur]
      apply d2 z
      obtain ⟨w3, h3, hq, hz'⟩ := hz
      rw [hrep, if_neg hne] at h3
      exact ⟨w3, h3, hq, hz'⟩
    · by_cases hri : r = i
      · subst r
        have hc0 : S.execCur i = [] := hidle.2
        rw [hH.execCur, hH.execIdx]
        exact ⟨fun _ => (s19 i hr).1 hc0, fun h => absurd hc0 h⟩
      · rw [hH.rep_other hri, hH.execCur, hH.execIdx]; exact s19 r hr
    · intro r hr a c y z hac h1 h2 ht
      rw [hH.execLog] at h1 h2; rw [hdE] at ht ⊢; rw [hsO]
      exact s20 r hr a c y z hac h1 h2 ht
    · obtain ⟨p1, p2, p3⟩ := s21
      refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
      · rw [hlx, hH.gexec]; exact p1 r hr k
      · rw [hlx, (hfl r).2.2.2.2.2]; exact p2 r hr k
      · rw [hlx] at h; rw [hH.gexec]; exact p3 r hr k pre e post h
  have hrepo : Inv.reports S' := reports_frame hsafeM (fun r m e h => (hprepR r m e).mp h)
    (fun r m e y b' st u hp h => hevB _ _ _ _ h hp.1
      (by rcases hp.2 with ⟨to, -, rfl⟩ | rfl <;> intro _ _ _ h <;> cases h))
    (fun r e hk h => hold r e h (fun y b' v' he => by subst he; cases hk)) s27
  have hrr : Inv.repliesReportVotes S' := by
    obtain ⟨q1, q2, q3⟩ := s9
    refine ⟨fun r m e hp => ?_, fun a r m hm' => ?_, fun a r m hm' => ?_⟩
    · have hp0 := (hprepR r m e).mp hp
      have hne : ∀ y b' v', e ≠ .commit y b' v' := by
        rcases hp0.2 with ⟨to, -, rfl⟩ | rfl <;> intro _ _ _ h <;> cases h
      obtain ⟨d1, d2, d3, d4, d5⟩ := q1 r m e hp0
      exact ⟨d1, fun hs => hH.evBefore_old (d2 hs), fun hs => (hcv' _ _).mpr (d3 hs),
        fun hs b' st u hb' => d4 hs b' st u (hevB _ _ _ _ hb' hp0.1 hne),
        fun b' st u hb' => d5 b' st u (by
          obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
          have hv' := hvote r _ b' st u (List.mem_of_getElem? h2)
          exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ hv' (fun _ _ _ h => by cases h)
            |> fun h => h)⟩
    · obtain ⟨d1, d2, d3, d4⟩ := q2 a r m ((hmsgs _ _ _).mp hm')
      refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
      · obtain ⟨u, hu⟩ := d1; exact ⟨u, hH.ev_old hu⟩
      · obtain ⟨e1, u, e2, e3⟩ := d2 hs; exact ⟨e1, u, hH.ev_old e2, e3⟩
      · obtain ⟨u, e2, e3⟩ := d3 hs; exact ⟨u, hH.ev_old e2, e3⟩
      · obtain ⟨u, e2, e3⟩ := d4 hs; exact ⟨u, (hcv' _ _).mpr e2, e3⟩
    · rcases q3 a r m ((hmsgs _ _ _).mp hm') with ⟨u, hu⟩ | ⟨⟨b', u, hu⟩, c2⟩
      · exact Or.inl ⟨u, hH.evBefore_old hu⟩
      · refine Or.inr ⟨⟨b', u, hH.evBefore_old hu⟩, fun m' e' hp hy hb' => ?_⟩
        have hp0 := (hprepR _ _ _).mp hp
        have hsent : S.ev a (.sent r (.acceptReply m)) := by
          obtain ⟨pp, pp', -, -, h1⟩ := hu; exact List.mem_of_getElem? h1
        exact c2 m' e' hp0 hy (hevB _ _ _ _ hb' hsent (fun _ _ _ h => by cases h))
  have hhi : Inv.prepReplyHighest S' := by
    intro r m e hp b' st u hb'
    have hp0 := (hprepR r m e).mp hp
    have hne : ∀ y b' v', e ≠ .commit y b' v' := by
      rcases hp0.2 with ⟨to, -, rfl⟩ | rfl <;> intro _ _ _ h <;> cases h
    exact s10 r m e hp0 b' st u (hevB _ _ _ _ hb' hp0.1 hne)
  have hown : Inv.ballotOwner S' := by
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := s6
    refine ⟨fun r y b' he => ?_, fun r y b' u he => ?_, fun r y b' u he => ?_,
      fun r to m hm' => ?_, fun r to m hm' => ?_, fun r to m hm' => ?_⟩
    · have h := hold r _ he (fun _ _ _ h => by cases h)
      refine ⟨(o1 r y b' h).1, ?_⟩
      rw [hH.count_eq (fun _ => hnotE _ (fun _ _ _ h => by cases h) rfl)]
      exact (o1 r y b' h).2
    · exact hH.evBefore_old (o2 r y b' u (hold r _ he (fun _ _ _ h => by cases h)))
    · exact hH.ev_old (o3 r y b' u (hold r _ he (fun _ _ _ h => by cases h)))
    · obtain ⟨d1, d2⟩ := o4 r to m ((hmsgs _ _ _).mp hm'); exact ⟨d1, hH.ev_old d2⟩
    · obtain ⟨d1, d2⟩ := o5 r to m ((hmsgs _ _ _).mp hm'); exact ⟨d1, hH.ev_old d2⟩
    · obtain ⟨d1, d2⟩ := o6 r to m ((hmsgs _ _ _).mp hm'); exact ⟨d1, hH.ev_old d2⟩
  have hop : Inv.oneProposal S' := by
    obtain ⟨p1, p2, p3⟩ := s7
    refine ⟨fun r r' y b' u u' he he' => ?_, fun r r' y b' u u' he he' => ?_,
      fun r r' y b' u u' he he' => ?_⟩
    · obtain ⟨d1, d2, d3⟩ := p1 r r' y b' u u' (hold r _ he (fun _ _ _ h => by cases h))
        (hold r' _ he' (fun _ _ _ h => by cases h))
      refine ⟨d1, d2, ?_⟩
      rw [hH.count_eq (fun _ => hnotE _ (fun _ _ _ h => by cases h) rfl)]; exact d3
    · exact p2 r r' y b' u u' (hold r _ he (fun _ _ _ h => by cases h))
        (hold r' _ he' (fun _ _ _ h => by cases h))
    · exact p3 r r' y b' u u' (hold r _ he (fun _ _ _ h => by cases h))
        (hold r' _ he' (fun _ _ _ h => by cases h))
  have hvf : Inv.votesFollowProposals S' := by
    refine ⟨fun r y b' st u he hst => ?_, fun r y b' u he => ?_⟩
    · obtain ⟨l, u0, h1, h2⟩ := s8.1 r y b' st u (hvote _ _ _ _ _ he) hst
      exact ⟨l, u0, hH.ev_old h1, h2⟩
    · obtain ⟨l, h1⟩ := s8.2 r y b' u (hvote _ _ _ _ _ he); exact ⟨l, hH.ev_old h1⟩
  have hdc : Inv.decidedChosen S' := by
    intro y u hu
    rcases s13 y u ((hcv' _ _).mp hu) with ⟨b', Q, q1, q2, q3⟩ | ⟨⟨Q, q1, q2, q3⟩, hf⟩
    · exact Or.inl ⟨b', Q, q1, q2, fun r hr => ⟨(q3 r hr).1, hH.ev_old (q3 r hr).2⟩⟩
    · refine Or.inr ⟨⟨Q, q1, q2, fun r hr => ?_⟩, hH.ev_old hf⟩
      obtain ⟨d1, d2, st, d3, d4⟩ := q3 r hr
      exact ⟨d1, d2, st, d3, hH.ev_old d4⟩
  have hdcv : Inv.depsCover S' := fun y z u u' hne h1 h2 hi' =>
    s15 y z u u' hne ((hcv' _ _).mp h1) ((hcv' _ _).mp h2) hi'
  have hwit : Inv.witnesses S' := by
    intro y u hu hn'
    obtain ⟨W, w1, w2, w3⟩ := s16 y u ((hcv' _ _).mp hu) hn'
    exact ⟨W, w1, w2, fun r hr => ⟨(w3 r hr).1, by
      obtain ⟨d, d1, d2⟩ := (w3 r hr).2; exact ⟨d, hH.ev_old d1, d2⟩⟩⟩
  have hac : Inv.attrsCover S' := by
    intro r e y cy z cz d hrec hne hb' hi'
    exact s17 r e y cy z cz d hrec hne (hevB _ _ _ _ hb'
      (by obtain ⟨pp, pp', -, -, h⟩ := hb'
          exact hold r _ (List.mem_of_getElem? h) (fun _ _ _ h => by cases h))
      (fun _ _ _ h => by cases h)) hi'
  have hslots : Inv.slots S' := by
    refine ⟨fun y u hu => ?_, fun y ps h p hp => ?_⟩
    · rw [hH.owner]; exact s22.1 y u ((hcv' _ _).mp hu)
    · rw [hH.owner] at h; rw [hH.ops]; exact s22.2 y ps h p hp
  have hco : Inv.clientOps S' := by
    have hso : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, hH.owner]
    exact ExecOrd.clientOps_frame s23 hH.ops hH.gexec hH.fired (fun _ _ _ => by rw [hso])
      (fun y v h => (hcv' _ _).mpr h)
  have hcm : Inv.commitMsgs S' := by
    intro fr to m hm'
    obtain ⟨r, b', h⟩ := s24 fr to m ((hmsgs _ _ _).mp hm')
    exact ⟨r, b', hH.ev_old h⟩
  have hpk : Inv.pendingKind S' := by
    intro r b' hb'
    rw [hH.pending] at hb'
    by_cases hr : r = i
    · subst hr; simp at hb'
    · rw [upd_other _ _ _ _ hr] at hb'; exact s25 r b' hb'
  have hrt : Inv.replyTargets S' := by
    intro fr to m y hm' hy hk'
    obtain ⟨w1, lb1, h1, hl1⟩ := s3 fr to m y ((hmsgs _ _ _).mp hm') hy hk'
    rcases R2 to y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
    · exact ⟨w', lb', R3, W7⟩
    · exact ⟨w1, lb1, h, hl1⟩
  refine ⟨⟨hwf, fun fr to m hm' => s2 fr to m ((hmsgs _ _ _).mp hm'), hrt,
    fun fr to m hm' => s4 fr to m ((hmsgs _ _ _).mp hm'), hbal, hown, hop, hvf, hrr, hhi, hlbI,
    hagr, hdc, chosenSafe_of_safe _ hwf hbal hown hvf hsafe, hdcv, hwit, hac, hexec.1,
    hexec.2.1, hexec.2.2.1, hexec.2.2.2, hslots, hco, hcm, hpk, hsafe, hrepo⟩, ?_⟩
  -- the auxiliary conjuncts
  have hlbv : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      (i = r ∧ x = y ∧ w' = w2 ∧ lb' = lb2) ∨
        ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
    intro r y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | h
    · rw [W7] at hl2; cases hl2; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr h
  have hnotPA : ¬ isPA lb'.status := by rw [k3]; rintro (h | h) <;> cases h
  exact {
    stRange := fun r hr y w2 h2 => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inr (Or.inr hcom'))
      · exact hA.stRange r hr y w2 h
    cmdsSome := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W1]; simp
      · exact hA.cmdsSome r hr y w2 h hs
    noneRec := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W4] at hs; cases hs
      · obtain ⟨d1, d2⟩ := hA.noneRec r hr y w2 h hs
        exact ⟨d1, fun b' st u hv0 => d2 b' st u (hvote _ _ _ _ _ hv0)⟩
    vbalNonneg := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W3]; exact hb0
      · exact hA.vbalNonneg r hr y w2 h hs
    votesLe := fun r hr y w2 h2 b' st u hv0 => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · obtain ⟨w1, h1, hle⟩ := s5.2 i hi x b' st u (hvote _ _ _ _ _ hv0)
        rw [hw] at h1; cases h1; rw [W3]; omega
      · exact hA.votesLe r hr y w2 h b' st u (hvote _ _ _ _ _ hv0)
    recVote := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W4] at hs; rcases hs with (h | h) | h <;> cases h
      · exact hH.ev_old (hA.recVote r hr y w2 h hs)
    accKeep := fun r hr y w2 h2 b' u hv0 hle => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact Or.inr hcom'
      · exact hA.accKeep r hr y w2 h b' u (hvote _ _ _ _ _ hv0) hle
    recCommit := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · exact ⟨b, v, hH.ev_new (by simp), by rw [W2]; exact Int.le_refl _⟩
      · obtain ⟨b', u, d1, d2⟩ := hA.recCommit r hr y w2 h hs
        exact ⟨b', u, hH.ev_old d1, d2⟩
    commitRec := fun r y b' u hr he => by
      rcases (hE r _).mp he with h | ⟨rfl, h⟩
      · obtain ⟨w1, h1, hs⟩ := hA.commitRec r y b' u hr h
        rcases R2 r y w1 h1 with ⟨-, -, rfl⟩ | h'
        · exact absurd hs hnc
        · exact ⟨w1, h', hs⟩
      · simp only [Event.commit.injEq] at h; obtain ⟨rfl, -, -⟩ := h
        exact ⟨w', R3, hcom'⟩
    fastCommitEv := fun r y u he => by
      obtain ⟨d1, b', d2⟩ := hA.fastCommitEv r y u (hold _ _ he (fun _ _ _ h => by cases h))
      exact ⟨d1, b', hH.ev_old d2⟩
    makerLb := fun r y b' hr he => by
      obtain ⟨w1, lb1, h1, hl1, hle⟩ :=
        hA.makerLb r y b' hr (hold _ _ he (fun _ _ _ h => by cases h))
      rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · rw [hlb] at hl1; cases hl1; exact ⟨w', lb', R3, W7, by rw [k1]; exact hle⟩
      · exact ⟨w1, lb1, h, hl1, hle⟩
    lastLeBal := fun r hr y w2 lb2 h2 hl2 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
      · rw [k1, W2]; exact hlt
      · exact hA.lastLeBal r hr y w2 lb2 h hl2
    peerOk := fun r hr => by rw [(hfl r).2.1]; exact hA.peerOk r hr
    crtOwn := fun r hr q hq => by rw [(hfl r).2.2.1, (hfl q).2.2.1]; exact hA.crtOwn r hr q hq
    crtRec := fun r hr y w2 h2 => by
      rw [(hfl y.q).2.2.1]
      rcases R1 r y w2 h2 with ⟨rfl, rfl, -⟩ | ⟨h, -⟩
      · exact hA.crtRec i hi x w hw
      · exact hA.crtRec r hr y w2 h
    crtMsg := fun fr to m y hm' hy => by
      rw [(hfl y.q).2.2.1]; exact hA.crtMsg fr to m y ((hmsgs _ _ _).mp hm') hy
    crtEv := fun r e y he hy => by
      rw [(hfl y.q).2.2.1]
      rcases (hE r e).mp he with h | ⟨-, rfl⟩
      · exact hA.crtEv r e y h hy
      · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨(s1.2.1 i hi x w hw).2.1, hA.crtRec i hi x w hw⟩
    ownRow := fun q hq j hj => by
      rw [(hfl q).2.2.1] at hj
      obtain ⟨w1, lb1, h1, hl1⟩ := hA.ownRow q hq j hj
      rcases R2 q _ w1 h1 with ⟨rfl, hx', rfl⟩ | h
      · exact ⟨w', lb', by rw [← hx']; exact R3, W7⟩
      · exact ⟨w1, lb1, h, hl1⟩
    paNoAcc := fun r hr y w2 lb2 h2 hl2 hs u hv0 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · exact hnotPA hs
      · exact hA.paNoAcc r hr y w2 lb2 h hl2 hs u (hold _ _ hv0 (fun _ _ _ h => by cases h))
    paLeader := fun r hr y w2 lb2 h2 hl2 hs hp hc' hb' => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnotPA
      · obtain ⟨u, hu⟩ := hp
        exact hA.paLeader r hr y w2 lb2 h hl2 hs ⟨u, hold _ _ hu (fun _ _ _ h => by cases h)⟩ hc' hb'
    prepNoProp := fun r hr y w2 lb2 h2 hl2 hp => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · rw [k4] at hp; cases hp
      · obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w2 lb2 h hl2 hp
        exact ⟨d1, fun u h' => d2 u (hold _ _ h' (fun _ _ _ h => by cases h)),
          fun u h' => d3 u (hold _ _ h' (fun _ _ _ h => by cases h)), d4, d5⟩
    paMsgOnce := fun fr to y b' => by rw [hcnt]; exact hA.paMsgOnce fr to y b'
    accMsgOnce := fun fr to y b' => by rw [hcnt]; exact hA.accMsgOnce fr to y b'
    paVoteDeliv := fun r y b' st u hst hv0 => by
      rcases hA.paVoteDeliv r y b' st u hst (hvote _ _ _ _ _ hv0) with ⟨u0, h0⟩ | h0
      · exact Or.inl ⟨u0, hH.ev_old h0⟩
      · exact Or.inr (fun fr' => hall _ _ _ (h0 fr'))
    parOnce := fun a r y b' h1 => by
      rw [hcnt] at h1 ⊢
      obtain ⟨d1, d2⟩ := hA.parOnce a r y b' h1
      exact ⟨d1, hall _ _ _ d2⟩
    arFrom := fun a r m hm' => by
      obtain ⟨b'', u, d1, d2⟩ := hA.arFrom a r m ((hmsgs _ _ _).mp hm')
      exact ⟨b'', u, d1, hH.ev_old d2⟩
    arOnce := fun a r y b' h1 => by
      rw [hcnt] at h1 ⊢
      rcases hA.arOnce a r y b' h1 with ⟨w1, lb1, h1', hl1, hlt'⟩ | ⟨d1, d2⟩
      · refine Or.inl ?_
        rcases R2 r y w1 h1' with ⟨rfl, rfl, rfl⟩ | h
        · rw [hlb] at hl1; cases hl1; exact ⟨w', lb', R3, W7, by rw [k1]; exact hlt'⟩
        · exact ⟨w1, lb1, h, hl1, hlt'⟩
      · exact Or.inr ⟨d1, hall _ _ _ d2⟩
    commitBal := fun fr to m hm' => hA.commitBal fr to m ((hmsgs _ _ _).mp hm')
    sentPR := fun r to m he => by
      have he0 := hold _ _ he (fun _ _ _ h => by cases h)
      obtain ⟨d1, d2, d3⟩ := hA.sentPR r to m he0
      refine ⟨fun hr => ?_, fun b' st u hb' => d2 b' st u ?_, fun to' m2 hb' hy => d3 to' m2 ?_ hy⟩
      · obtain ⟨w1, h1, hle⟩ := d1 hr
        rcases R2 r _ w1 h1 with ⟨rfl, hy, rfl⟩ | h
        · exact ⟨w', by rw [← hy]; exact R3, by rw [W2]; omega⟩
        · exact ⟨w1, h, hle⟩
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩
          (hvote _ _ _ _ _ (List.mem_of_getElem? h2)) (fun _ _ _ h => by cases h)
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩
          (hold _ _ (List.mem_of_getElem? h2) (fun _ _ _ h => by cases h))
          (fun _ _ _ h => by cases h)
    confCover := fun r hr e y cy he hrec c hc' => by
      rw [(hfl r).2.2.2.1]
      rcases (hE r e).mp he with h | ⟨-, rfl⟩
      · exact hA.confCover r hr e y cy h hrec c hc'
      · cases hrec
    classWf := fun r hr => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        by_cases h : r = i
        · subst h; rw [hH.rep_self]; exact hcls
        · rw [hH.rep_other h]; exact ⟨rfl, rfl⟩
      refine AuxProof.clsWf_keep (hA.classWf r hr) hcl.1 hcl.2 (fun y h => ?_)
      obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp h
      rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h2
      · rw [R3]; simp
      · rw [h2]; simp
    classCover := fun r hr e y cy he hrec => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        by_cases h : r = i
        · subst h; rw [hH.rep_self]; exact hcls
        · rw [hH.rep_other h]; exact ⟨rfl, rfl⟩
      rw [hcl.1, hcl.2]
      rcases (hE r e).mp he with h | ⟨-, rfl⟩
      · exact hA.classCover r hr e y cy h hrec
      · cases hrec
    paAttrs := fun r y b' st u hst hv0 =>
      hH.ev_old (hA.paAttrs r y b' st u hst (hvote _ _ _ _ _ hv0))
    valOk := fun r y b' u hv0 => by
      rw [hH.owner]
      exact hA.valOk r y b' u (hv0.imp (fun h => hold _ _ h (fun _ _ _ h => by cases h))
        (fun h => hold _ _ h (fun _ _ _ h => by cases h)))
    cmdsNe := by
      obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hA.cmdsNe
      refine ⟨fun fr to m hm' => m1 fr to m ((hmsgs _ _ _).mp hm'),
        fun r hr y w2 cs h2 hc' => ?_, fun r hr y w2 lb2 cs h2 hl2 hc' => ?_,
        fun fr to m hm' => m4 fr to m ((hmsgs _ _ _).mp hm'),
        fun r m he => m5 r m (hold _ _ he (fun _ _ _ h => by cases h)),
        fun r y b' u hv0 => m6 r y b' u (hv0.imp (fun h => hold _ _ h (fun _ _ _ h => by cases h))
          (fun h => hold _ _ h (fun _ _ _ h => by cases h)))⟩
      · rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
        · rw [W1] at hc'; cases hc'; exact hcne
        · exact m2 r hr y w2 cs h hc'
      · rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
        · rw [k10] at hc'; cases hc'; exact hcne
        · exact m3 r hr y w2 lb2 cs h hl2 hc'
    prSent := fun fr to m hm' => hH.ev_old (hA.prSent fr to m ((hmsgs _ _ _).mp hm'))
    selfOk := fun r m he hs => hA.selfOk r m (hold _ _ he (fun _ _ _ h => by cases h)) hs
    selfRaw := fun r m he => hA.selfRaw r m (hold _ _ he (fun _ _ _ h => by cases h))
    pm := by
      have hP := hA.pm
      have hlbo : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
          ¬ (r = i ∧ y = x) → (S.rep r).inst y = some w2 := by
        intro r y w2 lb2 h2 hl2 hne
        rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, -⟩ | ⟨h, -⟩
        · exact absurd ⟨rfl, rfl⟩ hne
        · exact h
      have hacc : ∀ r y c u, S'.ev r (.accept y c u) → S.ev r (.accept y c u) :=
        fun r y c u h => hold _ _ h (fun _ _ _ h => by cases h)
      have hph : ∀ r y c u, S'.ev r (.phase1 y c u) → S.ev r (.phase1 y c u) :=
        fun r y c u h => hold _ _ h (fun _ _ _ h => by cases h)
      have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
      have hbal : ∀ r y w1, (S.rep r).inst y = some w1 →
          ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w1.bal ≤ zz w2.bal := by
        intro r y w1 h1
        rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
        · exact ⟨w', R3, by rw [W2]; exact hb⟩
        · exact ⟨w1, h, Int.le_refl _⟩
      have hnotPA' : ¬ isPA lb'.status := hnotPA
      have hlt' : zz (initBal x) < zz b := Int.lt_of_lt_of_le hlI hlt
      exact {
        arOk := PMProof.arOk_frame hP (fun a r m h => (hmsgs _ _ _).mp h) hacc
          (fun q y c u h => Or.inl (hvote _ _ _ _ _ h)) hmono (fun y u h => (hcv' _ _).mpr h) hbal
        commitProp := fun r y c u he hle => by
          rcases (hE r _).mp he with h | ⟨-, h⟩
          · exact PMProof.propAt_mono hmono (hP.commitProp r y c u h hle)
          · simp only [Event.commit.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; omega
        commitMsgProp := PMProof.commitMsgProp_frame hP (fun fr to m h => (hmsgs _ _ _).mp h) hmono
        lbProp := fun r hr y w2 lb2 h2 hl2 hs hv => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · rw [k3] at hs; cases hs
          · obtain ⟨u, hu⟩ := hv
            exact PMProof.propAt_mono hmono (hP.lbProp r hr y w2 lb2 h hl2 hs ⟨u, hacc _ _ _ _ hu⟩)
        parCom := PMProof.parCom_frame hP (fun a r m h => (hmsgs _ _ _).mp h) hmono
        parSt := PMProof.parSt_frame hP (fun a r m h => (hmsgs _ _ _).mp h)
          (fun fr to m h => by rw [hH.sent]; exact h)
        paFresh := fun r hr y w2 lb2 h2 hl2 hs h0 hv => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · exact absurd hs hnotPA'
          · obtain ⟨u, hu⟩ := hv
            exact hP.paFresh r hr y w2 lb2 h hl2 hs h0 ⟨u, hph _ _ _ _ hu⟩
        paCmds := fun r hr y w2 lb2 h2 hl2 hs u hu => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · exact absurd hs hnotPA'
          · exact hP.paCmds r hr y w2 lb2 h hl2 hs u (hph _ _ _ _ hu)
        paSent := PMProof.ps_hs hP hH hidle.1 (fun to m h => by simp at h)
          (fun b h => by cases h) (fun y w2 lb2 h2 hl2 hlt2 => by
            rcases hlbv _ y w2 lb2 h2 hl2 with ⟨-, rfl, -, rfl⟩ | ⟨h, -⟩
            · rw [k1] at hlt2; rw [hlt2] at hlI; exact absurd hlI (Int.lt_irrefl _)
            · exact ⟨w2, lb2, h, hl2, hlt2, rfl⟩)
        pendPA := PMProof.pendPA_hs hP hH (fun b h => by cases h)
        paVoteMsg := PMProof.paVoteMsg_frame hP hvote (fun fr to m h => by rw [hH.sent]; exact h)
        parNoPA := PMProof.parNoPA_frame hP (fun a r m h => (hmsgs _ _ _).mp h) hvote
        aeF := fun r hr y w2 lb2 h2 hl2 hs hae => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · exact absurd hs hnotPA'
          · obtain ⟨a, a', m, m', h1, h2', h3⟩ := hP.aeF r hr y w2 lb2 h hl2 hs hae
            exact ⟨a, a', m, m', by rw [hH.sent]; exact h1, by rw [hH.sent]; exact h2', h3⟩
        repLead := PMProof.repLead_frame hP (fun r m e h => (hprepR r m e).mp h) hbal
        paGe := PMProof.paGe_frame hP hvote hph
        phAttrs := PMProof.phAttrs_frame hP hph hmono
        accWit := PMProof.accWit_frame hP hacc hmono (fun y u h => (hcv' _ _).mpr h)
        accVote := PMProof.accVote_frame hP hacc hmono
        cmdSafe := CmdSafeProof.cmdSafe_frame hP hsafeM hph
        accSup := CmdSafeProof.accSup_frame hP hmono hacc }
    ownerCrt := fun y ps h => by
      rw [hH.owner] at h; rw [(hfl y.q).2.2.1]; exact hA.ownerCrt y ps h
    execLo := AuxProof.execLo_of_eq hA.execLo (fun r _ => (hfl r).2.2.2.2.1)
    exec := ExecOrd.invExec_hs hS.1 hA.exec hH hidle hagr hchan (fun r y h => by rw [hrep, if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h; exact h h1; exact h h2) R3
      (fun w0 h0 hs => by rw [hw] at h0; cases h0; exact absurd hs hwnex)
      (fun lb2 hl hne => ⟨w, lb, hw, hlb, by rw [W7] at hl; cases hl; rw [k6] at hne; exact hne⟩) }

end RecCommitProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
