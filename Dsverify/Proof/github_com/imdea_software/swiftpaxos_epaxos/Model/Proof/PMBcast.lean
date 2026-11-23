/-
`InvPM` under a broadcast step (`Sys.bcastStep`): the PreAccept broadcast at the initial ballot
moves its message from the pending broadcast to the outbox and sets `lb.preAcceptsSent` to its
send count (`paSent`); everything else is a frame.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Bcast
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxFrame

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs BcastProof

namespace PMProof

theorem next_fields (b b' : Bcast) (a : Bool) (h : b.next a = some b') :
    b'.m = b.m ∧ b'.x = b.x ∧ b'.trackPA = b.trackPA ∧ b'.need = b.need ∧
      b'.sent = b.sent + (if a then 1 else 0) := by
  unfold Bcast.next at h
  cases hp : b.peers with
  | nil => rw [hp] at h; cases h
  | cons q ps =>
    rw [hp] at h
    cases a
    · simp only [Bool.false_eq_true, if_false] at h
      unfold Bcast.norm at h
      by_cases hc : ({ b with peers := ps } : Bcast).peers = [] ∨
          ({ b with peers := ps } : Bcast).need ≤ ({ b with peers := ps } : Bcast).sent
      · rw [if_pos hc] at h; cases h
      · rw [if_neg hc] at h; simp only [Option.some.injEq] at h; subst h; simp
    · simp only [if_true] at h
      unfold Bcast.norm at h
      by_cases hc : ({ b with peers := ps, sent := b.sent + 1 } : Bcast).peers = [] ∨
          ({ b with peers := ps, sent := b.sent + 1 } : Bcast).need ≤
            ({ b with peers := ps, sent := b.sent + 1 } : Bcast).sent
      · rw [if_pos hc] at h; cases h
      · rw [if_neg hc] at h; simp only [Option.some.injEq] at h; subst h; simp

theorem filter_succ_gen {p q : Nat → Bool} (c : Nat)
    (h : ∀ a, q a = true → p a = true ∨ a = c) :
    ∀ l : List Nat, l.Nodup →
      (l.filter q).length ≤ (l.filter p).length + (if c ∈ l then 1 else 0) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro hnd
    have ha : a ∉ l := (List.nodup_cons.mp hnd).1
    have ih' := ih (List.nodup_cons.mp hnd).2
    have hmono : (if c ∈ l then 1 else 0) ≤ (if c ∈ a :: l then 1 else 0) := by
      by_cases hc : c ∈ l
      · rw [if_pos hc, if_pos (List.mem_cons_of_mem _ hc)]; exact Nat.le_refl _
      · rw [if_neg hc]; omega
    by_cases hq : q a = true
    · by_cases hp : p a = true
      · simp only [List.filter_cons, hq, hp, if_true, List.length_cons]; omega
      · have hac : a = c := (h a hq).resolve_left hp
        subst hac
        have h1 : (if a ∈ l then 1 else 0) = 0 := if_neg ha
        have h2 : (if a ∈ a :: l then 1 else 0) = 1 := if_pos List.mem_cons_self
        simp only [List.filter_cons, hq, hp, if_true, Bool.false_eq_true, if_false,
          List.length_cons]
        omega
    · simp only [List.filter_cons, hq, Bool.false_eq_true, if_false]
      by_cases hp : p a = true
      · simp only [hp, if_true, List.length_cons]; omega
      · simp only [hp, Bool.false_eq_true, if_false]; omega

/-- A filter over `range nR` grows by at most one element when its predicate gains one. -/
theorem filter_succ {p q : Nat → Bool} (c : Nat)
    (h : ∀ a, q a = true → p a = true ∨ a = c) :
    ((List.range nR).filter q).length ≤ ((List.range nR).filter p).length + 1 := by
  have := filter_succ_gen c h (List.range nR) List.nodup_range
  split at this <;> omega


/-- A bookkeeping after `bcastRep`: the tracking broadcast's instance gets `preAcceptsSent` set
to the new send count, every other one is unchanged. -/
theorem bcastRep_lb (σ : RState) (b : Bcast) (a : Bool) (x : InstId) (w' : InstRec) (lb' : LbRec)
    (h : (bcastRep σ b a).inst x = some w') (hl : w'.lb = some lb') :
    ∃ w lb, σ.inst x = some w ∧ w.lb = some lb ∧
      lb' = (if a = true ∧ b.trackPA = true ∧ b.peers ≠ [] ∧ b.x = x then
        { lb with preAcceptsSent := W64 ((b.sent + 1 : Nat) : Int) } else lb) := by
  unfold bcastRep at h
  by_cases hc : a = true ∧ b.trackPA = true ∧ b.peers ≠ []
  · rw [if_pos hc] at h
    unfold setPreAcceptsSent at h
    cases hx : σ.inst b.x with
    | none =>
      rw [hx] at h
      have hxx : b.x ≠ x := by intro e; rw [e, h] at hx; cases hx
      refine ⟨w', lb', h, hl, ?_⟩
      rw [if_neg (fun h' => hxx h'.2.2.2)]
    | some w0 =>
      rw [hx] at h
      cases hl0 : w0.lb with
      | none =>
        simp only [hl0] at h
        have hxx : b.x ≠ x := by intro e; rw [e, h] at hx; cases hx; rw [hl] at hl0; cases hl0
        refine ⟨w', lb', h, hl, ?_⟩
        rw [if_neg (fun h' => hxx h'.2.2.2)]
      | some lb0 =>
        simp only [hl0, RState.setInst, upd_apply] at h
        by_cases hxx : x = b.x
        · subst hxx
          simp only [if_true, Option.some.injEq] at h
          subst h
          simp only [Option.some.injEq] at hl
          refine ⟨w0, lb0, hx, hl0, ?_⟩
          rw [if_pos ⟨hc.1, hc.2.1, hc.2.2, rfl⟩, hl]
        · simp only [hxx, if_false] at h
          refine ⟨w', lb', h, hl, ?_⟩
          rw [if_neg (fun h' => hxx h'.2.2.2.symm)]
  · rw [if_neg hc] at h
    refine ⟨w', lb', h, hl, ?_⟩
    rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1, h'.2.2.1⟩)]

/-- **`InvPM` under a broadcast step.** -/
theorem pm_bcast (S : Sys) (i : Nat) (b : Bcast) (a : Bool) (hP : InvPM S)
    (hb : S.pending i = some b) (hpe : b.peers ≠ []) (hlt : b.sent < b.need)
    (hkind : b.m.isBcast = true)
    (hmsg : ∀ fr to m, m ∈ (S.bcastStep i b a).msgs fr to → m ∈ S.msgs fr to)
    (hcv : ∀ y u, S.committedVal y u → (S.bcastStep i b a).committedVal y u) :
    InvPM (S.bcastStep i b a) := by
  obtain ⟨p, ps, hpp⟩ : ∃ p ps, b.peers = p :: ps := by
    cases h : b.peers with
    | nil => exact absurd h hpe
    | cons p ps => exact ⟨p, ps, rfl⟩
  have erep : (S.bcastStep i b a).rep = upd S.rep i (bcastRep (S.rep i) b a) := by
    simp only [Sys.bcastStep, hpp]; cases a <;> rfl
  have esent : (S.bcastStep i b a).sent = S.sent := by
    simp only [Sys.bcastStep, hpp]; cases a <;> rfl
  have epend : (S.bcastStep i b a).pending = upd S.pending i (b.next a) := by
    simp only [Sys.bcastStep, hpp]; cases a <;> rfl
  have eob : ∀ fr to, (S.bcastStep i b a).outbox fr to =
      S.outbox fr to ++ (if a = true ∧ fr = i ∧ to = p then [b.m] else []) := by
    intro fr to
    simp only [Sys.bcastStep, hpp]
    cases a
    · simp
    · simp only [Sys.emit, upd_apply]
      by_cases h1 : fr = i
      · subst h1; by_cases h2 : to = p
        · subst h2; simp
        · simp [h2]
      · simp [h1]
  have ehist : ∀ r e, (S.bcastStep i b a).ev r e ↔ S.ev r e ∨ (a = true ∧ r = i ∧ e = .sent p b.m) := by
    intro r e
    simp only [Sys.ev, Sys.bcastStep, hpp]
    cases a
    · simp
    · simp only [Sys.emit, List.mem_append, List.mem_singleton, Prod.mk.injEq, true_and]
  have hnotPR : ∀ q, b.m ≠ .prepareReply q := by
    intro q h; rw [h] at hkind; cases hkind
  -- the records: only `preAcceptsSent` of `b.x`'s bookkeeping at `i` may change
  have hrel : ∀ r y w', ((S.bcastStep i b a).rep r).inst y = some w' →
      ∃ w, (S.rep r).inst y = some w ∧ PasRel w w' := by
    intro r y w' h
    rw [erep] at h
    by_cases hr : r = i
    · subst hr; rw [upd_same] at h; exact (bcastRep_inst _ _ _ _).1 w' h
    · rw [upd_other _ _ _ _ hr] at h; exact ⟨w', h, Or.inl rfl⟩
  have hrel2 : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w', ((S.bcastStep i b a).rep r).inst y = some w' ∧ PasRel w w' := by
    intro r y w h
    rw [erep]
    by_cases hr : r = i
    · subst hr; rw [upd_same]; exact (bcastRep_inst _ _ _ _).2 w h
    · rw [upd_other _ _ _ _ hr]; exact ⟨w, h, Or.inl rfl⟩
  have hlbm : ∀ r x w' lb', ((S.bcastStep i b a).rep r).inst x = some w' → w'.lb = some lb' →
      ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ LbPM lb lb' := by
    intro r x w' lb' h hl
    obtain ⟨w, hw, hr⟩ := hrel r x w' h
    obtain ⟨lb, hlb, e⟩ := (PasRel.fields hr).2.2.2.2.2.2.2.2 lb' hl
    refine ⟨w, lb, hw, hlb, ?_⟩
    rcases e with rfl | ⟨n, rfl⟩
    · exact LbPM.refl _
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpa' : ∀ r b', (S.bcastStep i b a).pending r = some b' → ∀ x c, b'.m.isPAat x c = true →
      b'.trackPA = true ∧ b'.x = x := by
    intro r b' hb' x c hc
    rw [epend] at hb'
    by_cases hr : r = i
    · subst hr; rw [upd_same] at hb'
      obtain ⟨e1, e2, e3, -, -⟩ := next_fields b b' a hb'
      rw [e1] at hc
      obtain ⟨h1, h2⟩ := hP.pendPA _ b hb x c hc
      exact ⟨by rw [e3]; exact h1, by rw [e2]; exact h2⟩
    · rw [upd_other _ _ _ _ hr] at hb'; exact hP.pendPA r b' hb' x c hc
  refine pm_frame' hP (fun r e h => (ehist r e).mpr (Or.inl h)) (fun r e h => ?_) hmsg
    (fun fr to m h => by rw [esent]; exact h) hcv
    (fun r y w h => by
      obtain ⟨w', hw', hr⟩ := hrel2 r y w h
      exact ⟨w', hw', by rw [(PasRel.fields hr).2.1]; exact Int.le_refl _⟩) hlbm ?_ hpa'
  · rcases (ehist r e).mp h with h | ⟨-, -, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, b.m, rfl, hnotPR⟩
  -- `paSent`
  intro x w' lb' hq hw' hlb' hlt'
  have hlbX : ∃ w lb, (S.rep x.q).inst x = some w ∧ w.lb = some lb ∧
      lb' = (if a = true ∧ x.q = i ∧ b.trackPA = true ∧ b.x = x then
        { lb with preAcceptsSent := W64 ((b.sent + 1 : Nat) : Int) } else lb) := by
    rw [erep] at hw'
    by_cases hqi : x.q = i
    · rw [hqi, upd_same] at hw'
      obtain ⟨w, lb, h1, h2, h3⟩ := bcastRep_lb _ b a x w' lb' hw' hlb'
      refine ⟨w, lb, by rw [hqi]; exact h1, h2, ?_⟩
      rw [h3]
      by_cases hc : a = true ∧ b.trackPA = true ∧ b.x = x
      · rw [if_pos ⟨hc.1, hc.2.1, hpe, hc.2.2⟩, if_pos ⟨hc.1, hqi, hc.2.1, hc.2.2⟩]
      · rw [if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.2⟩), if_neg (fun h => hc ⟨h.1, h.2.2.1, h.2.2.2⟩)]
    · rw [upd_other _ _ _ _ hqi] at hw'
      exact ⟨w', lb', hw', hlb', by rw [if_neg (fun h => hqi h.2.1)]⟩
  obtain ⟨w, lb, hw, hlb, e⟩ := hlbX
  have hlt : lb.lastTriedBallot = initBal x := by
    rw [e] at hlt'; split at hlt'
    · exact hlt'
    · exact hlt'
  obtain ⟨s1, s2, s3⟩ := hP.paSent x w lb hq hw hlb hlt
  -- the recipients: the outbox of `i` to `p` may gain `b.m`
  have hrc : ∀ a', ((S.bcastStep i b a).sent x.q a' ++ (S.bcastStep i b a).outbox x.q a').any
      (Msg.isPAat x (initBal x)) = true →
      (S.sent x.q a' ++ S.outbox x.q a').any (Msg.isPAat x (initBal x)) = true ∨
        (a = true ∧ x.q = i ∧ a' = p ∧ b.m.isPAat x (initBal x) = true) := by
    intro a' h
    obtain ⟨m, hm, hpm⟩ := List.any_eq_true.mp h
    rw [esent, eob] at hm
    simp only [List.mem_append] at hm
    rcases hm with hm | hm | hm
    · exact Or.inl (List.any_eq_true.mpr ⟨m, List.mem_append_left _ hm, hpm⟩)
    · exact Or.inl (List.any_eq_true.mpr ⟨m, List.mem_append_right _ hm, hpm⟩)
    · split at hm
      · rename_i hc; simp only [List.mem_singleton] at hm; subst hm
        exact Or.inr ⟨hc.1, hc.2.1, hc.2.2, hpm⟩
      · cases hm
  by_cases hcase : a = true ∧ x.q = i ∧ b.x = x ∧ b.trackPA = true
  · -- the tracking broadcast of `x` sends to `p`
    obtain ⟨ha, hqi, hbx, ht⟩ := hcase
    have hpb : S.pending x.q = some b := by rw [hqi]; exact hb
    obtain ⟨hpa, hs, hn⟩ := s2 b hpb hbx ht
    have hlb'eq : lb'.preAcceptsSent = W64 ((b.sent + 1 : Nat) : Int) := by
      rw [e, if_pos ⟨ha, hqi, ht, hbx⟩]
    have hnat : (W64 ((b.sent + 1 : Nat) : Int)).toNat = b.sent + 1 := by
      have : b.sent + 1 ≤ 2 * fR - 1 := by omega
      simp only [fR] at this
      show (BitVec.ofInt 64 ((b.sent : Int) + 1)).toNat = b.sent + 1
      rw [BitVec.toNat_ofInt]; omega
    · rw [hlb'eq, hnat]
      refine ⟨by omega, fun b' hb' hbx' ht' => ?_, ?_⟩
      · rw [epend, hqi, upd_same] at hb'
        obtain ⟨e1, e2, e3, e4, e5⟩ := next_fields b b' a hb'
        rw [ha] at e5
        refine ⟨by rw [e1]; exact hpa, by rw [e5, hs]; simp, by rw [e4]; exact hn⟩
      · have := filter_succ (p := fun a' => (S.sent x.q a' ++ S.outbox x.q a').any
            (Msg.isPAat x (initBal x))) p (fun a' h => by
              rcases hrc a' h with h | ⟨-, -, h, -⟩
              · exact Or.inl h
              · exact Or.inr h)
        unfold Sys.paRcpt; unfold Sys.paRcpt at s3; omega
  · have hlbeq : lb' = lb := by
      rw [e, if_neg (fun h => hcase ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩)]
    subst hlbeq
    refine ⟨s1, fun b' hb' hbx' ht' => ?_, ?_⟩
    · rw [epend] at hb'
      by_cases hqi : x.q = i
      · rw [hqi, upd_same] at hb'
        obtain ⟨e1, e2, e3, e4, e5⟩ := next_fields b b' a hb'
        have hbx : b.x = x := by rw [← e2]; exact hbx'
        have ht : b.trackPA = true := by rw [← e3]; exact ht'
        have ha : a = false := by
          cases a
          · rfl
          · exact absurd ⟨rfl, hqi, hbx, ht⟩ hcase
        obtain ⟨hpa, hs, hn⟩ := s2 b (by rw [hqi]; exact hb) hbx ht
        rw [ha] at e5
        exact ⟨by rw [e1]; exact hpa, by rw [e5, hs]; simp, by rw [e4]; exact hn⟩
      · rw [upd_other _ _ _ _ hqi] at hb'; exact s2 b' hb' hbx' ht'
    · refine Nat.le_trans (List.Sublist.length_le (filter_sub (fun a' h => ?_))) s3
      rcases hrc a' h with h | ⟨ha, hqi, -, hpm⟩
      · exact h
      · exfalso
        obtain ⟨ht, hbx⟩ := hP.pendPA i b hb x _ hpm
        exact hcase ⟨ha, hqi, hbx, ht⟩

end PMProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
