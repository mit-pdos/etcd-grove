/-
The Paxos `SafeAt` conjunct `Inv.safe`: `chosenSafe` follows from it (`chosenSafe_of_safe`), and
it is kept by every step whose replicas' `bal`s only grow, whose new votes are at ballots at least
the voter's `bal`, and whose new fast commits are by a leader whose `bal` is at most the initial
ballot (`SafeMono`), given that its new Accepts and Phase 1s are themselves safe.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace SafeProof

/-! ## Words -/

theorem zz_W32 (q : Int) (h1 : -2^31 ≤ q) (h2 : q < 2^31) : zz (W32 q) = q := by
  simp only [zz, sint.Z, W32, BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le] <;> omega

theorem eq_W32_of_zz (b : w32) (q : Int) (h1 : -2^31 ≤ q) (h2 : q < 2^31) (h : zz b = q) :
    b = W32 q := by
  apply BitVec.eq_of_toInt_eq
  simp only [zz, sint.Z] at h
  rw [h, BitVec.toInt_ofInt, Int.bmod_eq_of_le] <;> omega

theorem zz_initBal (x : InstId) (hq : x.q < nR) : zz (initBal x) = x.q := by
  unfold initBal; rw [zz_W32] <;> simp [nR] at hq ⊢ <;> omega

theorem zz_inj {b b' : w32} (h : zz b = zz b') : b = b' := BitVec.eq_of_toInt_eq h

/-! ## Counting -/

/-- Two duplicate-free lists inside a duplicate-free universe `U` whose lengths add up past
`U`'s meet. -/
theorem meet {Q Q' U : List Nat} (hQ : Q.Nodup) (hQ' : Q'.Nodup) (hs : ∀ a ∈ Q, a ∈ U)
    (hs' : ∀ a ∈ Q', a ∈ U) (hl : U.length < Q.length + Q'.length) : ∃ a, a ∈ Q ∧ a ∈ Q' := by
  refine Classical.byContradiction fun hne => ?_
  have hd : (Q ++ Q').Nodup := by
    rw [List.nodup_append]
    refine ⟨hQ, hQ', fun a ha b hb hab => hne ⟨a, ha, hab ▸ hb⟩⟩
  have hsub : (Q ++ Q').Subperm U := List.subperm_of_subset hd (by
    intro a ha; rcases List.mem_append.mp ha with h | h
    · exact hs a h
    · exact hs' a h)
  have := hsub.length_le
  rw [List.length_append] at this
  omega

/-- Two majorities of the `N` replicas meet. -/
theorem meet_maj {Q Q' : List Nat} (hQ : Q.Nodup) (hQ' : Q'.Nodup) (hs : ∀ a ∈ Q, a < nR)
    (hs' : ∀ a ∈ Q', a < nR) (hl : nR / 2 + 1 ≤ Q.length) (hl' : nR / 2 + 1 ≤ Q'.length) :
    ∃ a, a ∈ Q ∧ a ∈ Q' :=
  meet (U := List.range nR) hQ hQ' (fun a h => List.mem_range.mpr (hs a h))
    (fun a h => List.mem_range.mpr (hs' a h)) (by simp [nR] at hl hl' ⊢; omega)

/-- `2F - 1` and two replicas other than the leader meet. -/
theorem meet_fast {Q B : List Nat} (c : Nat) (hc : c < nR) (hQ : Q.Nodup) (hB : B.Nodup)
    (hs : ∀ a ∈ Q, a < nR ∧ a ≠ c) (hs' : ∀ a ∈ B, a < nR ∧ a ≠ c) (hl : 2 * fR - 1 ≤ Q.length)
    (hl' : 2 ≤ B.length) : ∃ a, a ∈ Q ∧ a ∈ B := by
  have hU : ((List.range nR).filter (· ≠ c)).length = nR - 1 := by
    have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by simp only [nR] at hc; omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  refine meet (U := (List.range nR).filter (· ≠ c)) hQ hB ?_ ?_ ?_
  · intro a h; obtain ⟨h1, h2⟩ := hs a h; simp [List.mem_filter, h1, h2]
  · intro a h; obtain ⟨h1, h2⟩ := hs' a h; simp [List.mem_filter, h1, h2]
  · rw [hU]; simp [nR, fR] at hl hl' ⊢; omega

/-! ## `chosenSafe` from `safe` -/

/-- A chosen ballot is real (its votes follow an Accept, made by its ballot's owner). -/
theorem slowChosen_real (S : Sys) (hbal : Inv.ballots S) (hwf : Inv.wf S)
    (hown : Inv.ballotOwner S) (hvf : Inv.votesFollowProposals S) (x : InstId) (b : w32) (v : Val)
    (h : S.slowChosen x b v) : realBal x b ∧ x.q < nR := by
  obtain ⟨Q, -, hl, hQ⟩ := h
  obtain ⟨r, hr⟩ : ∃ r, r ∈ Q := by
    cases Q with
    | nil => simp [nR] at hl
    | cons r _ => exact ⟨r, List.mem_cons_self⟩
  obtain ⟨hrn, hv⟩ := hQ r hr
  obtain ⟨w, hw, -⟩ := hbal.2 r hrn x b _ v hv
  have hxq := (hwf.2.1 r hrn x w hw).2.1
  obtain ⟨ℓ, hacc⟩ := hvf.2 r x b v hv
  have hmb := hown.2.2.1 ℓ x b v hacc
  rcases (hown.1 ℓ x b hmb).1 with ⟨h1, -⟩ | ⟨h1, -⟩
  · refine ⟨Or.inl ?_, hxq⟩
    unfold initBal
    exact eq_W32_of_zz b x.q (by omega) (by simp [nR] at hxq; omega) h1
  · exact ⟨Or.inr h1, hxq⟩

theorem not_slowChosen_of_blocked (S : Sys) (x : InstId) (b : w32) (v : Val)
    (hc : S.slowChosen x b v) (hb : S.blocked x b v) : False := by
  obtain ⟨Q, hQ, hl, hQm⟩ := hc
  obtain ⟨Q', hQ', hl', hQm'⟩ := hb
  obtain ⟨a, ha, ha'⟩ := meet_maj hQ hQ' (fun a h => (hQm a h).1) (fun a h => (hQm' a h).1) hl hl'
  exact (hQm' a ha').2.1 (hQm a ha).2

theorem not_fastLive_of_fastBlocked (S : Sys) (x : InstId) (v : Val) (hq : x.q < nR)
    (hc : S.fastLive x v) (hb : S.fastBlocked x v) : False := by
  obtain ⟨⟨Q, hQ, hl, hQm⟩, hlive⟩ := hc
  rcases hb with ⟨B, hB, hl', hBm⟩ | ⟨⟨wl, hwl, hlt⟩, hnf⟩
  · obtain ⟨a, ha, ha'⟩ := meet_fast x.q hq hQ hB (fun a h => ⟨(hQm a h).1, (hQm a h).2.1⟩)
      (fun a h => ⟨(hBm a h).1, (hBm a h).2.1⟩) hl hl'
    obtain ⟨-, -, st, hst, hv⟩ := hQm a ha
    exact (hBm a ha').2.2.1 st hst hv
  · rcases hlive with h | h
    · rw [hwl] at h; simp only [Option.map_some, Option.some.injEq] at h
      rw [h] at hlt; exact Int.lt_irrefl _ hlt
    · exact hnf h

theorem fastReplies_q (S : Sys) (hbal : Inv.ballots S) (hwf : Inv.wf S) (x : InstId) (v : Val)
    (h : S.fastReplies x v) : x.q < nR := by
  obtain ⟨Q, -, hl, hQ⟩ := h
  obtain ⟨r, hr⟩ : ∃ r, r ∈ Q := by
    cases Q with
    | nil => simp [fR] at hl
    | cons r _ => exact ⟨r, List.mem_cons_self⟩
  obtain ⟨hrn, -, st, -, hv⟩ := hQ r hr
  obtain ⟨w, hw, -⟩ := hbal.2 r hrn x _ st v hv
  exact (hwf.2.1 r hrn x w hw).2.1

theorem chosenSafe_of_safe (S : Sys) (hwf : Inv.wf S) (hbal : Inv.ballots S)
    (hown : Inv.ballotOwner S) (hvf : Inv.votesFollowProposals S) (hs : Inv.safe S) :
    Inv.chosenSafe S := by
  intro x b v hch b' hlt
  rcases hch with hc | ⟨rfl, hf⟩
  · obtain ⟨hreal, -⟩ := slowChosen_real S hbal hwf hown hvf x b v hc
    refine ⟨fun r v' he => ?_, fun r v' he => ?_⟩
    · refine Classical.byContradiction fun hne => ?_
      exact not_slowChosen_of_blocked S x b v hc ((hs.1 r x b' v' he).1 b hreal hlt v (Ne.symm hne))
    · exact not_slowChosen_of_blocked S x b v hc ((hs.2 r x b' v' he).1 b hreal hlt v)
  · have hq := fastReplies_q S hbal hwf x v hf.1
    refine ⟨fun r v' he => ?_, fun r v' he => ?_⟩
    · refine Classical.byContradiction fun hne => ?_
      exact not_fastLive_of_fastBlocked S x v hq hf ((hs.1 r x b' v' he).2 hlt v (Ne.symm hne))
    · exact not_fastLive_of_fastBlocked S x v hq hf ((hs.2 r x b' v' he).2 hlt v)

/-! ## Stability -/

/-- What a step's new vote satisfies: it is at a ballot at least the voter's `bal`; a pre-accept
vote at the initial ballot needs the instance below ACCEPTED, and, at a non-leader, a PreAccept
at the initial ballot sent to it; a pre-accept vote repeats no other pre-accept vote at its
ballot. -/
def NewVote (S : Sys) (r : Nat) (x : InstId) (b : w32) (st : w8) (v : Val) : Prop :=
  (∀ w, (S.rep r).inst x = some w → zz w.bal ≤ zz b ∧
    (isPA st → b = initBal x → stGe w.status stACCEPTED = false)) ∧
  (isPA st → ∀ st' u, isPA st' → S.ev r (.vote x b st' u) → u = v) ∧
  (isPA st → b = initBal x → r ≠ x.q → ∃ m : PreAccept, Msg.preAccept m ∈ S.msgs x.q r ∧
    (Msg.preAccept m).instOf = some x ∧ m.ballot = initBal x)

/-- A step after which `blocked`/`fastBlocked` facts stay true: `bal`s only grow (instances are
never removed) and an instance at least ACCEPTED stays so unless its `bal` passes the initial
ballot; events are kept; new votes are `NewVote`s; a new fast commit is by a leader whose `bal`
is at most the initial ballot; a new PreAccept at the initial ballot comes before its Phase 1. -/
structure SafeMono (S S' : Sys) : Prop where
  bal : ∀ r x w, (S.rep r).inst x = some w →
    ∃ w', (S'.rep r).inst x = some w' ∧ zz w.bal ≤ zz w'.bal ∧
      (stGe w.status stACCEPTED = true →
        stGe w'.status stACCEPTED = true ∨ zz (initBal x) < zz w'.bal)
  hist : ∀ r e, S.ev r e → S'.ev r e
  vote : ∀ r x b st v, S'.ev r (.vote x b st v) → S.ev r (.vote x b st v) ∨ NewVote S r x b st v
  fast : ∀ x v, S'.ev x.q (.fastCommit x v) →
    S.ev x.q (.fastCommit x v) ∨ ∀ w, (S.rep x.q).inst x = some w → zz w.bal ≤ zz (initBal x)
  pa : ∀ a x (m : PreAccept), Msg.preAccept m ∈ S'.msgs x.q a → (Msg.preAccept m).instOf = some x →
    m.ballot = initBal x →
    Msg.preAccept m ∈ S.msgs x.q a ∨ ∀ v0, ¬ S.ev x.q (.phase1 x (initBal x) v0)

theorem blocked_mono {S S' : Sys} (hm : SafeMono S S') {x : InstId} {b : w32} {w : Val}
    (h : S.blocked x b w) : S'.blocked x b w := by
  obtain ⟨Q, hQ, hl, hQm⟩ := h
  refine ⟨Q, hQ, hl, fun a ha => ?_⟩
  obtain ⟨han, hnv, wa, hwa, hlt⟩ := hQm a ha
  obtain ⟨wa', hwa', hle, -⟩ := hm.bal a x wa hwa
  refine ⟨han, fun hv => ?_, wa', hwa', Int.lt_of_lt_of_le hlt hle⟩
  rcases hm.vote a x b _ w hv with h | ⟨h, -⟩
  · exact hnv h
  · have := (h wa hwa).1; omega

theorem noPA_mono {S S' : Sys} (hm : SafeMono S S') {x : InstId} {a : Nat} {w : Val}
    (ha : a ≠ x.q) (h : S.noPA x a w) : S'.noPA x a w := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun st hst hv => ?_, ?_⟩
  · rcases hm.vote a x _ st w hv with h | ⟨n1, n2, n3⟩
    · exact h1 st hst h
    · rcases h2 with ⟨wa, hwa, hlt | hge⟩ | ⟨st', u, hst', hne, hv'⟩ | ⟨-, hno⟩
      · have := (n1 wa hwa).1; omega
      · rw [(n1 wa hwa).2 hst rfl] at hge; cases hge
      · exact hne (n2 hst st' u hst' hv')
      · obtain ⟨m, hm', hx, hb⟩ := n3 hst rfl ha
        exact hno m hm' hx hb
  · rcases h2 with ⟨wa, hwa, hc⟩ | ⟨st', u, hst', hne, hv'⟩ | ⟨⟨v0, hp⟩, hno⟩
    · obtain ⟨wa', hwa', hle, hs⟩ := hm.bal a x wa hwa
      refine Or.inl ⟨wa', hwa', ?_⟩
      rcases hc with hlt | hge
      · exact Or.inl (Int.lt_of_lt_of_le hlt hle)
      · rcases hs hge with h | h
        · exact Or.inr h
        · exact Or.inl h
    · exact Or.inr (Or.inl ⟨st', u, hst', hne, hm.hist _ _ hv'⟩)
    · refine Or.inr (Or.inr ⟨⟨v0, hm.hist _ _ hp⟩, fun m hm' hx hb => ?_⟩)
      rcases hm.pa a x m hm' hx hb with h | h
      · exact hno m h hx hb
      · exact absurd hp (h v0)

theorem fastBlocked_mono {S S' : Sys} (hm : SafeMono S S') {x : InstId} {w : Val}
    (h : S.fastBlocked x w) : S'.fastBlocked x w := by
  rcases h with ⟨B, hB, hl, hBm⟩ | ⟨⟨wl, hwl, hlt⟩, hnf⟩
  · refine Or.inl ⟨B, hB, hl, fun a ha => ?_⟩
    obtain ⟨han, hq, hno⟩ := hBm a ha
    exact ⟨han, hq, noPA_mono hm hq hno⟩
  · obtain ⟨wl', hwl', hle, -⟩ := hm.bal x.q x wl hwl
    refine Or.inr ⟨⟨wl', hwl', Int.lt_of_lt_of_le hlt hle⟩, fun hf => ?_⟩
    rcases hm.fast x w hf with h | h
    · exact hnf h
    · have := h wl hwl; omega

theorem safeAcc_mono {S S' : Sys} (hm : SafeMono S S') {x : InstId} {b' : w32} {v' : Val}
    (h : S.safeAcc x b' v') : S'.safeAcc x b' v' :=
  ⟨fun b hr hlt w hw => blocked_mono hm (h.1 b hr hlt w hw),
   fun hlt w hw => fastBlocked_mono hm (h.2 hlt w hw)⟩

theorem safePh_mono {S S' : Sys} (hm : SafeMono S S') {x : InstId} {b' : w32}
    (h : S.safePh x b') : S'.safePh x b' :=
  ⟨fun b hr hlt w => blocked_mono hm (h.1 b hr hlt w),
   fun hlt w => fastBlocked_mono hm (h.2 hlt w)⟩

/-- `safe` is kept by a `SafeMono` step whose new Accepts and Phase 1s are safe. -/
theorem safe_step {S S' : Sys} (hm : SafeMono S S') (hs : Inv.safe S)
    (hacc : ∀ r x b' v', S'.ev r (.accept x b' v') → S.ev r (.accept x b' v') ∨ S'.safeAcc x b' v')
    (hph : ∀ r x b' v', S'.ev r (.phase1 x b' v') → S.ev r (.phase1 x b' v') ∨ S'.safePh x b') :
    Inv.safe S' := by
  refine ⟨fun r x b' v' he => ?_, fun r x b' v' he => ?_⟩
  · rcases hacc r x b' v' he with h | h
    · exact safeAcc_mono hm (hs.1 r x b' v' h)
    · exact h
  · rcases hph r x b' v' he with h | h
    · exact safePh_mono hm (hs.2 r x b' v' h)
    · exact h

/-- `safe` is kept by a `SafeMono` step that makes no Accept or Phase 1. -/
theorem safe_frame {S S' : Sys} (hm : SafeMono S S') (hs : Inv.safe S)
    (hacc : ∀ r x b' v', S'.ev r (.accept x b' v') → S.ev r (.accept x b' v'))
    (hph : ∀ r x b' v', S'.ev r (.phase1 x b' v') → S.ev r (.phase1 x b' v')) :
    Inv.safe S' :=
  safe_step hm hs (fun r x b' v' he => Or.inl (hacc r x b' v' he))
    (fun r x b' v' he => Or.inl (hph r x b' v' he))

/-- The events `safe` reads. -/
def safeKind : Event → Bool
  | .vote .. | .accept .. | .phase1 .. | .fastCommit .. => true
  | _ => false

/-- A step that keeps every replica's instance `bal`s and makes no vote, Accept, Phase 1 or fast
commit event keeps `safe`. -/
theorem safeMono_same (S S' : Sys)
    (hbal : ∀ r x w, (S.rep r).inst x = some w → ∃ w', (S'.rep r).inst x = some w' ∧
      w'.bal = w.bal ∧ (stGe w.status stACCEPTED = true → stGe w'.status stACCEPTED = true))
    (hhist : ∀ r e, S.ev r e → S'.ev r e)
    (hev : ∀ r e, safeKind e = true → S'.ev r e → S.ev r e)
    (hmsgs : ∀ fr to m, m ∈ S'.msgs fr to → m ∈ S.msgs fr to) : SafeMono S S' := by
  refine ⟨fun r x w h => ?_, hhist, fun r x b st v h => Or.inl (hev r _ rfl h),
    fun x v h => Or.inl (hev _ _ rfl h), fun a x m h _ _ => Or.inl (hmsgs _ _ _ h)⟩
  obtain ⟨w', h1, h2, h3⟩ := hbal r x w h
  exact ⟨w', h1, by rw [h2]; exact Int.le_refl _, fun h => Or.inl (h3 h)⟩

theorem safe_same (S S' : Sys)
    (hbal : ∀ r x w, (S.rep r).inst x = some w → ∃ w', (S'.rep r).inst x = some w' ∧
      w'.bal = w.bal ∧ (stGe w.status stACCEPTED = true → stGe w'.status stACCEPTED = true))
    (hhist : ∀ r e, S.ev r e → S'.ev r e)
    (hev : ∀ r e, safeKind e = true → S'.ev r e → S.ev r e)
    (hmsgs : ∀ fr to m, m ∈ S'.msgs fr to → m ∈ S.msgs fr to)
    (hs : Inv.safe S) : Inv.safe S' :=
  safe_frame (safeMono_same S S' hbal hhist hev hmsgs) hs (fun r x b' v' he => hev r _ rfl he)
    (fun r x b' v' he => hev r _ rfl he)

/-- `reports` is kept by a `SafeMono` step that makes no report, no vote, Accept or fast
commit, and orders no new vote before an old report. -/
theorem reports_frame {S S' : Sys} (hm : SafeMono S S')
    (hprep : ∀ r m e, S'.prepReport r m e → S.prepReport r m e)
    (hevB : ∀ r m e x b st u, S.prepReport r m e → S'.evBefore r (.vote x b st u) r e →
      S.evBefore r (.vote x b st u) r e)
    (hev : ∀ r e, safeKind e = true → S'.ev r e → S.ev r e)
    (h : Inv.reports S) : Inv.reports S' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := h
  refine ⟨fun r m e hp => c1 r m e (hprep r m e hp), fun r m e hp => c2 r m e (hprep r m e hp),
    fun r m e hp => c3 r m e (hprep r m e hp),
    fun r m e hp b u hb => c4 r m e (hprep r m e hp) b u (hevB r m e _ b _ u (hprep r m e hp) hb),
    fun r m e hr hp => ?_,
    fun r x b st st' v v' h1 h2 h3 h4 => c6 r x b st st' v v' h1 h2 (hev r _ rfl h3) (hev r _ rfl h4),
    fun x v m e h1 h2 h3 => c7 x v m e (hev _ _ rfl h1) (hprep _ m e h2) h3,
    fun r x v h1 w => fastBlocked_mono hm (c8 r x v (hev r _ rfl h1) w),
    fun r m e hp => c9 r m e (hprep r m e hp)⟩
  obtain ⟨w, hw, hle⟩ := c5 r m e hr (hprep r m e hp)
  obtain ⟨w', hw', hle', -⟩ := hm.bal r _ w hw
  exact ⟨w', hw', Int.le_trans hle hle'⟩

end SafeProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
