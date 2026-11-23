/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Protocol.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
From the protocol invariant to the recovery's facts: quorums, AQ a majority, reports' facts (class-0 entries, R[0]'s entries, the fast path's paths and dependencies), the recovery's context, and ballot safety by strong induction on the ballot.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Safety

@[expose] public section

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-! ## Quorums -/

theorem nodup_bound (l : List Nat) (N : Nat) (hnd : l.Nodup) (h : ∀ r ∈ l, r < N) : l.length ≤ N := by
  have hsub : l ⊆ List.range N := fun r hr => List.mem_range.mpr (h r hr)
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

/-- Two majorities meet. -/
theorem majority_meet (N : Nat) (Q1 Q2 : List Nat) (h1 : isMajority N Q1) (h2 : isMajority N Q2) :
    ∃ r, r ∈ Q1 ∧ r ∈ Q2 := by
  apply Classical.byContradiction
  intro hno
  have hdisj : ∀ r ∈ Q1, r ∉ Q2 := fun r hr hr2 => hno ⟨r, hr, hr2⟩
  have hnd : (Q1 ++ Q2).Nodup := List.nodup_append.mpr ⟨h1.1, h2.1, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
  have := nodup_bound (Q1 ++ Q2) N hnd (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact h1.2.1 r hr
    · exact h2.2.1 r hr)
  have := h1.2.2; have := h2.2.2
  simp at *; omega

theorem combos_sub : ∀ (k : Nat) (l : List Nat), ∀ q ∈ combos k l, List.Sublist q l ∧ q.length = k := by
  intro k l
  induction l generalizing k with
  | nil => intro q hq; cases k <;> simp [combos] at hq <;> subst hq <;> simp
  | cons a l ih =>
    intro q hq
    cases k with
    | zero => simp [combos] at hq; subst hq; simp
    | succ k =>
      simp only [combos, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q', hq', rfl⟩ | hq
      · obtain ⟨h1, h2⟩ := ih k q' hq'; exact ⟨h1.cons₂ a, by simp [h2]⟩
      · obtain ⟨h1, h2⟩ := ih (k + 1) q hq; exact ⟨h1.cons a, h2⟩

theorem combos_complete : ∀ (k : Nat) (l : List Nat) (q : List Nat), List.Sublist q l → q.length = k → q ∈ combos k l := by
  intro k l
  induction l generalizing k with
  | nil => intro q hq hk; cases hq; subst hk; simp [combos]
  | cons a l ih =>
    intro q hq hk
    cases k with
    | zero => cases q with
      | nil => simp [combos]
      | cons _ _ => simp at hk
    | succ k =>
      simp only [combos, List.mem_append, List.mem_map]
      cases hq with
      | cons _ h => exact Or.inr (ih (k + 1) q h hk)
      | cons_cons _ h => exact Or.inl ⟨_, ih k _ h (by simpa using hk), rfl⟩

theorem range_sublist_witness (N L : Nat) (hL : L < N) :
    ∃ q, List.Sublist q (List.range N) ∧ q.length = N / 2 + 1 ∧ L ∈ q := by
  by_cases h : L < N / 2 + 1
  · exact ⟨List.range (N / 2 + 1), List.range_sublist.mpr (by omega), by simp, List.mem_range.mpr h⟩
  · refine ⟨List.range (N / 2) ++ [L], ?_, by simp, by simp⟩
    have e : List.range N = List.range (N / 2) ++ (List.range (N - N / 2)).map (N / 2 + ·) := by
      rw [← List.range_add]; congr 1; omega
    rw [e]
    apply List.Sublist.append (List.Sublist.refl _)
    rw [List.singleton_sublist, List.mem_map]
    exact ⟨L - N / 2, List.mem_range.mpr (by omega), by omega⟩

/-- The fast quorum of a ballot is a majority containing its leader. -/
theorem AQ_majority (N b : Nat) (hN : 0 < N) : isMajority N (AQ N b) ∧ leaderOf N b ∈ AQ N b := by
  unfold AQ
  have hL : leaderOf N b < N := Nat.mod_lt _ hN
  obtain ⟨q, hq, hql, hLq⟩ := range_sublist_witness N (leaderOf N b) hL
  have hmem : q ∈ (combos (N / 2 + 1) (List.range N)).filter (fun q => leaderOf N b ∈ q) := by
    rw [List.mem_filter]; exact ⟨combos_complete _ _ q hq hql, by simp [hLq]⟩
  generalize hl : (combos (N / 2 + 1) (List.range N)).filter (fun q => leaderOf N b ∈ q) = lqs at hmem
  have hpos : 0 < lqs.length := List.length_pos_of_mem hmem
  have hi : (b / N) % lqs.length < lqs.length := Nat.mod_lt _ hpos
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp only [Option.getD_some]
  have hin : lqs[(b / N) % lqs.length] ∈ lqs := List.getElem_mem hi
  have hin' : lqs[(b / N) % lqs.length] ∈ (combos (N / 2 + 1) (List.range N)).filter
      (fun q => leaderOf N b ∈ q) := by rw [hl]; exact hin
  rw [List.mem_filter] at hin'
  obtain ⟨hc, hLin⟩ := hin'
  obtain ⟨hsub, hlen⟩ := combos_sub _ _ _ hc
  simp only [decide_eq_true_eq] at hLin
  refine ⟨⟨hsub.nodup List.nodup_range, fun r hr => List.mem_range.mp (hsub.subset hr), by omega⟩, hLin⟩

/-! ## `recOrder`'s and reports' small facts -/

theorem recOrderStep_sub (k : Kept) (ids placed : List CmdId) (y : CmdId)
    (h : y ∈ recOrderStep k ids placed) : y ∈ placed ∨ y ∈ ids := by
  unfold recOrderStep at h
  dsimp only at h
  split at h
  · rename_i c x hc
    simp at h; rcases h with h | rfl
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.mp (List.mem_of_find?_eq_some hc)).1
  · rename_i c hn hc
    simp at h; rcases h with h | rfl
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.mp (List.mem_of_mem_head? hc)).1
  · exact Or.inl h

theorem recOrder_sub (k : Kept) (ids : List CmdId) (x : CmdId) (h : x ∈ recOrder k ids) : x ∈ ids := by
  rw [recOrder_eq] at h
  have : ∀ n, ∀ y ∈ iter (recOrderStep k ids) n [], y ∈ ids := by
    intro n
    induction n with
    | zero => intro y hy; simp [iter] at hy
    | succ n ih =>
      intro y hy
      rw [iter_succ'] at hy
      rcases recOrderStep_sub k ids _ y hy with h | h
      · exact ih y h
      · exact h
  exact this _ x h

theorem base_mem (S : PState) (c : Nat) (x : CmdId) (h : x ∈ S.base c) :
    ∃ M, S.sync c = some M ∧ x ∈ M.map Prod.fst := by
  unfold PState.base at h
  cases hs : S.sync c with
  | none => rw [hs] at h; simp at h
  | some M =>
    rw [hs] at h; simp only [Option.map_some, Option.getD_some] at h
    refine ⟨M, rfl, ?_⟩
    have := recOrder_sub _ _ x h
    unfold sortIds at this; exact List.mem_mergeSort.mp this

theorem recPos_idx (r0 : Nat × Report) (c : CmdId) (h : c ∈ r0.2.entries.map (·.id)) :
    recPos r0 c = some ((r0.2.entries.map (·.id)).idxOf c) := by
  unfold recPos
  generalize r0.2.entries = es at h ⊢
  induction es with
  | nil => simp at h
  | cons e es ih =>
    rw [List.findIdx?_cons, List.map_cons, List.idxOf_cons]
    by_cases he : e.id = c
    · simp [he]
    · have h' : c ∈ es.map (·.id) := by simp at h ⊢; rcases h with h | h; exact absurd h.symm he; exact h
      simp [he, ih h']

theorem U_mem (reps : List (Nat × Report)) (a : Nat × Report) (h : a ∈ recU (recAcks reps)) :
    a ∈ reps ∧ a.2.cbal = recMaxC (recAcks reps) := by
  unfold recU at h; rw [List.mem_filter] at h
  exact ⟨List.mem_mergeSort.mp h.1, by simpa using h.2⟩

theorem cbal_le_max (acks : List (Nat × Report)) (a : Nat × Report) (h : a ∈ acks) :
    a.2.cbal ≤ recMaxC acks := by
  unfold recMaxC
  have gen : ∀ (l : List Nat) (m : Nat), ∀ v ∈ l, v ≤ l.foldl max m := by
    intro l
    induction l with
    | nil => intro m v hv; simp at hv
    | cons w l ih =>
      intro m v hv
      simp only [List.foldl_cons]
      simp at hv; rcases hv with rfl | hv
      · have : ∀ (l : List Nat) (m : Nat), m ≤ l.foldl max m := by
          intro l; induction l with
          | nil => intro m; exact Nat.le_refl _
          | cons u l ih' => intro m; exact Nat.le_trans (Nat.le_max_left m u) (ih' _)
        exact Nat.le_trans (Nat.le_max_right m v) (this l _)
      · exact ih _ v hv
  exact gen _ 0 _ (List.mem_map.mpr ⟨a, h, rfl⟩)

theorem max_attained (acks : List (Nat × Report)) (h : acks ≠ []) :
    ∃ a ∈ acks, a.2.cbal = recMaxC acks := by
  unfold recMaxC
  have gen : ∀ (l : List Nat) (m : Nat), l.foldl max m = m ∨ l.foldl max m ∈ l := by
    intro l
    induction l with
    | nil => intro m; left; rfl
    | cons w l ih =>
      intro m; simp only [List.foldl_cons]
      rcases ih (max m w) with h | h
      · rw [h]; rcases Nat.le_total m w with hw | hw
        · right; rw [Nat.max_eq_right hw]; simp
        · left; exact Nat.max_eq_left hw
      · right; simp [h]
  rcases gen (acks.map (·.2.cbal)) 0 with h0 | h0
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil acks h
    refine ⟨a, ha, ?_⟩
    have := cbal_le_max acks a ha; unfold recMaxC at this; rw [h0] at this ⊢; omega
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp h0; exact ⟨a, ha, he⟩

theorem depsIn_loc (S : PState) (l : List CmdId) (hnd0 : l.Nodup) (hreg : ∀ y ∈ l, S.cmds y ≠ none)
    {y d : CmdId} (hd : d ∈ depsIn (S.seqOf l) y) :
    precedes l d y ∧ ∃ cd cy, S.cmds d = some cd ∧ S.cmds y = some cy ∧ cd.key = cy.key := by
  obtain ⟨t, q, u, hs, hqy, hdt⟩ := depsIn_mem _ y d hd
  have hfst := Ctx.seqOf_fst (S := S) l hreg
  rw [hs] at hfst
  have hnd := hnd0; rw [← hfst] at hnd
  have hq : q.1 ∉ t.map Prod.fst := by
    simp only [List.map_append, List.map_cons, List.nodup_append] at hnd
    intro h; exact hnd.2.2 q.1 h q.1 (by simp) rfl
  refine ⟨?_, ?_⟩
  · rw [← hfst, ← hqy]; simp only [List.map_append, List.map_cons]
    exact precedes_split _ _ _ _ hq hdt
  · unfold depsIn at hd
    rw [hs, ← hqy, cmdIn_split t u q hq, before_split t u q hq] at hd
    simp only at hd
    obtain ⟨t1, q', t2, ht, hq'd, hk, -⟩ := (mem_lkDeps t q.2 d).mp hd
    have hq'mem : q' ∈ S.seqOf l := by rw [hs, ht]; simp
    have hqmem : q ∈ S.seqOf l := by rw [hs]; simp
    exact ⟨q'.2, q.2, hq'd ▸ (Ctx.mem_seqOf hq'mem).1, hqy ▸ (Ctx.mem_seqOf hqmem).1, hk⟩

/-- A base command's dependencies (in the leader's order) are base commands. -/
theorem base_deps (S : PState) (l : List CmdId) (B : List CmdId) (hB : B <+: l) (hnd : l.Nodup)
    (hreg : ∀ y ∈ l, S.cmds y ≠ none) {y d : CmdId} (hy : y ∈ B) (hd : d ∈ depsIn (S.seqOf l) y) :
    d ∈ B := by
  have hp := (depsIn_loc S l hnd hreg hd).1
  obtain ⟨R', rfl⟩ := hB
  obtain ⟨B1, B2, rfl⟩ := List.append_of_mem hy
  have hyB1 : y ∉ B1 := by
    intro h; have := hnd; simp only [List.append_assoc, List.cons_append, List.nodup_append, List.nodup_cons] at this
    exact this.2.2 y h y (by simp) rfl
  have : (B1 ++ y :: B2 ++ R').takeWhile (· != y) = B1 := by
    rw [List.append_assoc, List.cons_append]; exact takeWhile_split B1 _ y hyB1
  unfold precedes at hp; rw [this] at hp
  simp [hp]

theorem precedes_append_not (B H : List CmdId) (z y : CmdId) (hy : y ∉ B) :
    precedes (B ++ H) z y ↔ z ∈ B ∨ precedes H z y := by
  unfold precedes
  rw [List.takeWhile_append_of_pos]
  · simp
  · intro a ha; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; intro h; subst h; exact hy ha

namespace PState
variable {S : PState} {N : Nat}

theorem repOk_parts {r b' : Nat} {R : Report} (h : S.repOk N r b' R) :
    (S.rs r).ballot ≥ b' ∧ R.cbal < b' ∧
    (0 < R.cbal → ∃ M, S.sync R.cbal = some M ∧ ∀ p ∈ M, ∃ e ∈ R.entries, e.id = p.1 ∧
      e.phase.toNat = 3 ∧ e.dep.Perm p.2.2) ∧
    (∀ c' x, R.cbal < c' → c' < b' → ¬ S.acc r c' x ∧ S.pre r c' x = none ∧ ¬ S.com r c' x ∧
      S.loc r c' = []) ∧
    (∀ x, S.acc r R.cbal x ∨ S.com r R.cbal x → ∃ e ∈ R.entries, e.id = x ∧
      (e.phase.toNat ≥ 2 ∨ (r = leaderOf N R.cbal ∧ e.phase.toNat ≥ 1))) ∧
    (∀ x D, S.pre r R.cbal x = some D → ∃ e ∈ R.entries, e.id = x ∧
      (e.phase.toNat ≥ 2 ∨ (e.phase.toNat = 1 ∧ e.dep = D))) ∧
    (r = leaderOf N R.cbal → ∀ x ∈ S.ord N R.cbal, ∃ e ∈ R.entries, e.id = x) ∧
    (∃ B, B.Perm (S.base R.cbal) ∧
      R.entries.map (·.id) = B ++ (S.loc r R.cbal).drop (S.base R.cbal).length) ∧
    (∀ e ∈ R.entries, S.entryOk N r R.cbal e) := h

end PState

namespace PState
variable {S : PState} {N : Nat} {fr : Bool}

/-- A base command is executed (`handleSync`). -/
theorem lexec_of_base {c : Nat} {x : CmdId} (h : x ∈ S.base c) : S.lexec N c x :=
  ⟨[x], by simp, fun y hy => by simp at hy; subst hy; exact Or.inl h⟩

/-- An executed command is a base command or one the leader pre-accepted. -/
theorem lexec_cases {c : Nat} {x : CmdId} (h : S.lexec N c x) :
    x ∈ S.base c ∨ ∃ D, S.pre (leaderOf N c) c x = some D := by
  obtain ⟨E, hx, hE⟩ := h
  rcases hE x hx with h | ⟨D, hD, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨D, hD⟩

/-- The leader's dependencies of an executed command are executed. -/
theorem lexec_deps (hI : S.PInv N fr) {c : Nat} {x d : CmdId} (h : S.lexec N c x)
    (hd : d ∈ depsIn (S.ordSeq N c) x) : S.lexec N c d := by
  obtain ⟨E, hx, hE⟩ := h
  rcases hE x hx with hb | ⟨D, hD, hDE⟩
  · apply lexec_of_base
    obtain ⟨M, hM, -⟩ := base_mem S _ _ hb
    obtain ⟨-, -, hpre, -⟩ := hI.sync_ok _ M hM
    exact base_deps S _ _ hpre (hI.loc_ok _ _).1 (hI.loc_ok _ _).2.1 hb hd
  · obtain ⟨-, -, -, hD', -⟩ := hI.pre_ok _ _ _ _ hD
    refine ⟨E, hDE d ?_, hE⟩
    rw [hD']; exact hd

/-- Execution only grows. -/
theorem lexec_le' {S' : PState} (hsync : ∀ b M, S.sync b = some M → S'.sync b = some M)
    (hpre : ∀ r b x D, S.pre r b x = some D → S'.pre r b x = some D) {c : Nat} {x : CmdId}
    (h : S.lexec N c x) : S'.lexec N c x := by
  obtain ⟨E, hx, hE⟩ := h
  refine ⟨E, hx, fun y hy => ?_⟩
  rcases hE y hy with hb | ⟨D, hD, hDE⟩
  · left
    unfold PState.base at hb ⊢
    cases hs : S.sync c with
    | none => rw [hs] at hb; simp at hb
    | some M => rw [hs] at hb; rw [hsync c M hs]; exact hb
  · exact Or.inr ⟨D, hpre _ _ _ _ hD, hDE⟩

end PState

theorem recPos_mem {r0 : Nat × Report} {z : CmdId} {i : Nat} (h : recPos r0 z = some i) :
    z ∈ r0.2.entries.map (·.id) := by
  have := List.findIdx?_eq_some_iff_getElem.mp h
  obtain ⟨hi, hp, -⟩ := this
  simp at hp
  exact List.mem_map.mpr ⟨_, List.getElem_mem hi, hp⟩

theorem recPos_lt {r0 : Nat × Report} {z y : CmdId} {i j : Nat} (hz : recPos r0 z = some i)
    (hy : recPos r0 y = some j) (hlt : i < j) : precedes (r0.2.entries.map (·.id)) z y := by
  have hzm := recPos_mem hz
  rw [recPos_idx r0 z hzm] at hz
  rw [recPos_idx r0 y (recPos_mem hy)] at hy
  cases hz; cases hy
  exact (precedes_iff _ _ _).mpr ⟨hzm, hlt⟩

theorem base_prefix_ord {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) (c : Nat) :
    S.base c <+: S.ord N c := by
  unfold PState.base
  cases hs : S.sync c with
  | none => exact List.nil_prefix
  | some M => have := (hI.sync_ok c M hs).2.2.1; unfold PState.base at this; rw [hs] at this; exact this

/-- `keyPrefix` through the handled part's order. -/
theorem mem_keyPrefix (S : PState) (r b : Nat) (H : List CmdId) (hloc : S.loc r b = S.base b ++ H)
    (hreg : ∀ y ∈ H, S.cmds y ≠ none) (x z : CmdId) (cx cz : Cmd) (hcx : S.cmds x = some cx)
    (hcz : S.cmds z = some cz) :
    z ∈ S.keyPrefix r b x ↔ z = x ∨ (precedes H z x ∧ cz.key = cx.key) := by
  unfold PState.keyPrefix
  rw [hcx, hloc]
  simp only [List.drop_left]
  have : (S.seqOf H).takeWhile (fun p => p.1 != x) = S.seqOf (H.takeWhile (· != x)) :=
    PState.seqOf_takeWhile S H x hreg
  rw [this]
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_singleton, beq_iff_eq]
  constructor
  · rintro (⟨q, ⟨hq, hk⟩, rfl⟩ | h)
    · right
      obtain ⟨hqc, hqm⟩ := Ctx.mem_seqOf (S := S) (y := q.1) (c := q.2) (by simpa using hq)
      rw [hcz] at hqc; cases hqc
      exact ⟨hqm, hk⟩
    · exact Or.inl h
  · rintro (h | ⟨hp, hk⟩)
    · exact Or.inr h
    · left
      refine ⟨(z, cz), ⟨?_, hk⟩, rfl⟩
      unfold PState.seqOf; exact List.mem_filterMap.mpr ⟨z, hp, by simp [hcz]⟩

section derive
variable {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) {b' : Nat}
  {reps : List (Nat × Report)} (hrep : ∀ p ∈ reps, S.rep p.1 b' = some p.2)

include hI hrep

/-- Reporters of the highest `cballot`: their reports' facts. -/
theorem U_rep {a : Nat × Report} (ha : a ∈ recU (recAcks reps)) :
    a.2.cbal = recMaxC (recAcks reps) ∧ S.repOk N a.1 b' a.2 := by
  obtain ⟨h1, h2⟩ := U_mem reps a ha
  exact ⟨h2, hI.rep_ok a.1 b' a.2 (hrep a h1)⟩

theorem K0_of_acc {a : Nat × Report} (ha : a ∈ recU (recAcks reps)) {d : CmdId}
    (h : S.acc a.1 (recMaxC (recAcks reps)) d ∨ S.com a.1 (recMaxC (recAcks reps)) d) :
    K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) d := by
  obtain ⟨hc, hok⟩ := U_rep hI hrep ha
  obtain ⟨-, -, -, -, hacc, -, -, -, hent⟩ := PState.repOk_parts hok
  rw [hc] at hacc
  obtain ⟨e, he, hid, hph⟩ := hacc d h
  have := (hent e he).2.2.1
  refine ⟨a, ha, e, he, hid, ?_⟩
  unfold okPhase
  cases hph with
  | inl hph => simp; omega
  | inr hph => simp [hph.1]; omega

theorem K0_of_base {a : Nat × Report} (ha : a ∈ recU (recAcks reps)) {d : CmdId}
    (h : d ∈ S.base (recMaxC (recAcks reps))) :
    K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) d := by
  obtain ⟨hc, hok⟩ := U_rep hI hrep ha
  obtain ⟨-, -, hbase, -⟩ := PState.repOk_parts hok
  rw [hc] at hbase
  obtain ⟨M, hM, hd⟩ := base_mem S _ d h
  have hpos : 0 < recMaxC (recAcks reps) := (hI.sync_ok _ M hM).1
  obtain ⟨M', hM', hall⟩ := hbase hpos
  rw [hM] at hM'; cases hM'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
  obtain ⟨e, he, hid, hph, -⟩ := hall p hp
  exact ⟨a, ha, e, he, hid, by unfold okPhase; simp [hph]⟩

/-- A command the old leader pre-accepted is class 0, if it reported. -/
theorem K0_of_pre {a : Nat × Report} (ha : a ∈ recU (recAcks reps))
    (hL : a.1 = leaderOf N (recMaxC (recAcks reps))) {d : CmdId} {D : List CmdId}
    (h : S.pre a.1 (recMaxC (recAcks reps)) d = some D) :
    K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) d := by
  obtain ⟨hc, hok⟩ := U_rep hI hrep ha
  obtain ⟨-, -, -, -, -, hpre, -, -, hent⟩ := PState.repOk_parts hok
  rw [hc] at hpre
  obtain ⟨e, he, hid, hph⟩ := hpre d D h
  have := (hent e he).2.2.1
  refine ⟨a, ha, e, he, hid, ?_⟩
  rcases hph with hph | ⟨hph, -⟩ <;> (unfold okPhase; simp [hL]; omega)

/-- D33: a command the old leader executed is class 0, if it reported. -/
theorem K0_of_lexec {a : Nat × Report} (ha : a ∈ recU (recAcks reps))
    (hL : a.1 = leaderOf N (recMaxC (recAcks reps))) {d : CmdId}
    (h : S.lexec N (recMaxC (recAcks reps)) d) :
    K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) d := by
  rcases PState.lexec_cases h with hb | ⟨D, hD⟩
  · exact K0_of_base hI hrep ha hb
  · rw [← hL] at hD; exact K0_of_pre hI hrep ha hL hD

/-- A class-0 entry: in the leader's order, with its dependencies. -/
theorem K0_entry {a : Nat × Report} (ha : a ∈ recU (recAcks reps)) {e : RepEntry}
    (he : e ∈ a.2.entries) (hok : okPhase (leaderOf N (recMaxC (recAcks reps))) a e = true) :
    e.id ∈ S.ord N (recMaxC (recAcks reps)) ∧
      e.dep.Perm (depsIn (S.seqOf (S.ord N (recMaxC (recAcks reps)))) e.id) := by
  obtain ⟨hc, hrok⟩ := U_rep hI hrep ha
  obtain ⟨-, -, -, -, -, -, -, -, hent⟩ := PState.repOk_parts hrok
  rw [hc] at hent
  obtain ⟨hcmd, hloc, hph3, h2, h1, -⟩ := hent e he
  unfold okPhase at hok
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hok
  rcases hok with (hok | hok) | ⟨hL, hok⟩
  · exact (h2 (by omega)).2
  · exact (h2 (by omega)).2
  · rcases h1 hok with ⟨-, h⟩ | hpre
    · exact h
    · obtain ⟨-, -, hx, hD, -⟩ := hI.pre_ok a.1 (recMaxC (recAcks reps)) e.id e.dep hpre
      rw [hL] at hx hD
      exact ⟨hx, by rw [hD]; rfl⟩

/-- A class-0 entry's dependencies: earlier ones, class 0 if the old leader did not report;
if it did (D33), reported by it (a dropped proposal of the old leader is a dependency of a
class-0 entry, but not of class 0 itself). -/
theorem K0_dep {a : Nat × Report} (ha : a ∈ recU (recAcks reps)) {e : RepEntry}
    (he : e ∈ a.2.entries) (hok : okPhase (leaderOf N (recMaxC (recAcks reps))) a e = true) :
    ∀ d ∈ e.dep, d ≠ e.id ∧ (K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) d ∨
      ((recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps))) = true ∧
        ∃ a' ∈ recU (recAcks reps), ∃ e' ∈ a'.2.entries, e'.id = d)) := by
  have hent' := K0_entry hI hrep ha he hok
  obtain ⟨hc, hrok⟩ := U_rep hI hrep ha
  obtain ⟨-, -, -, -, -, -, -, -, hent⟩ := PState.repOk_parts hrok
  rw [hc] at hent
  obtain ⟨hcmd, hloc, hph3, h2, h1, -⟩ := hent e he
  have hordnd := (hI.loc_ok (leaderOf N (recMaxC (recAcks reps))) (recMaxC (recAcks reps))).1
  have hordreg := (hI.loc_ok (leaderOf N (recMaxC (recAcks reps))) (recMaxC (recAcks reps))).2.1
  unfold okPhase at hok
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hok
  intro d hd
  have hd' : d ∈ depsIn (S.seqOf (S.ord N (recMaxC (recAcks reps)))) e.id := hent'.2.mem_iff.mp hd
  have hprec := (depsIn_loc S _ hordnd hordreg hd').1
  refine ⟨fun h => precedes_irrefl _ _ (h ▸ hprec), ?_⟩
  have hdord : d ∈ S.ord N (recMaxC (recAcks reps)) := precedes_mem _ _ _ hprec
  by_cases hLU : ∃ a' ∈ recU (recAcks reps), a'.1 = leaderOf N (recMaxC (recAcks reps))
  · right
    obtain ⟨a', ha', hal⟩ := hLU
    refine ⟨List.any_eq_true.mpr ⟨a', ha', by simp [hal]⟩, a', ha', ?_⟩
    obtain ⟨hc', hrok'⟩ := U_rep hI hrep ha'
    obtain ⟨-, -, -, -, -, -, hlead, -, -⟩ := PState.repOk_parts hrok'
    rw [hc'] at hlead
    exact hlead hal d hdord
  · left
    have notL : a.1 ≠ leaderOf N (recMaxC (recAcks reps)) := fun h => hLU ⟨a, ha, h⟩
    have viaAcc : S.acc a.1 (recMaxC (recAcks reps)) e.id →
        K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) d := by
      intro hacc
      obtain ⟨-, -, -, -, hN2⟩ := hI.acc_ok _ _ _ hacc
      exact K0_of_acc hI hrep ha (hN2 notL d hd')
    rcases hok with (hok | hok) | ⟨hL, hok⟩
    rotate_left 2
    · exact absurd hL notL
    all_goals
      rcases (h2 (by omega)).1 with hacc | hcom
      · exact viaAcc hacc
      · obtain ⟨-, -, -, hcases⟩ := hI.com_ok _ _ _ hcom
        rcases hcases with hL | hacc | hbase
        · exact absurd hL notL
        · exact viaAcc hacc
        · apply K0_of_base hI hrep ha
          obtain ⟨M, hM, -⟩ := base_mem S _ _ hbase
          obtain ⟨-, -, hpre, -⟩ := hI.sync_ok _ M hM
          exact base_deps S _ _ hpre hordnd hordreg hbase hd'
/-- A reporter of the highest `cballot`: its report lists the base, then what it handled. -/
theorem rep_structure {a : Nat × Report} (ha : a ∈ recU (recAcks reps)) :
    ∃ B H, a.2.entries.map (·.id) = B ++ H ∧ B.Perm (S.base (recMaxC (recAcks reps))) ∧
      S.loc a.1 (recMaxC (recAcks reps)) = S.base (recMaxC (recAcks reps)) ++ H ∧
      (S.loc a.1 (recMaxC (recAcks reps))).Nodup := by
  obtain ⟨hc, hrok⟩ := U_rep hI hrep ha
  obtain ⟨-, -, -, -, -, -, -, ⟨B, hB, hids⟩, hent⟩ := PState.repOk_parts hrok
  rw [hc] at hB hids
  have hnd := (hI.loc_ok a.1 (recMaxC (recAcks reps))).1
  have hpre : S.base (recMaxC (recAcks reps)) <+: S.loc a.1 (recMaxC (recAcks reps)) := by
    by_cases hl : S.loc a.1 (recMaxC (recAcks reps)) = []
    · -- nothing handled: no entry, so no base
      have hnil : a.2.entries = [] := by
        cases he : a.2.entries with
        | nil => rfl
        | cons e _ =>
          have := (hent e (by rw [he]; simp)).2.1; rw [hc, hl] at this; simp at this
      rw [hnil] at hids; simp at hids
      rw [hids.1] at hB
      rw [← List.Perm.nil_eq hB]; exact List.nil_prefix
    · by_cases h0 : recMaxC (recAcks reps) = 0
      · have : S.base (recMaxC (recAcks reps)) = [] := by
          unfold PState.base; cases hs : S.sync (recMaxC (recAcks reps)) with
          | none => rfl
          | some M => have := (hI.sync_ok _ M hs).1; omega
        rw [this]; exact List.nil_prefix
      · exact ((hI.loc_ok a.1 _).2.2 hl).2.2 (by omega) |>.2
  refine ⟨B, (S.loc a.1 (recMaxC (recAcks reps))).drop (S.base (recMaxC (recAcks reps))).length,
    hids, hB, ?_, hnd⟩
  obtain ⟨t, ht⟩ := hpre
  rw [← ht]; simp

/-- `R[0]`'s entries other than class-0 ones depend on commands it reported earlier, of their
key. -/
theorem R0_facts {r0 : Nat × Report} (hr0 : r0 ∈ recU (recAcks reps)) :
    (r0.2.entries.map (·.id)).Nodup ∧
    ∀ e ∈ r0.2.entries, ¬ K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) e.id →
      ∀ d ∈ e.dep, d ≠ e.id ∧ (∃ e' ∈ r0.2.entries, e'.id = d) ∧
        (∃ pd pe, recPos r0 d = some pd ∧ recPos r0 e.id = some pe ∧ pd < pe) ∧
        (∃ cd, S.cmds d = some cd ∧ cd.key = e.cmd.key) := by
  obtain ⟨B, H, hids, hB, hloc, hnd⟩ := rep_structure hI hrep hr0
  obtain ⟨hc, hrok⟩ := U_rep hI hrep hr0
  obtain ⟨-, -, -, -, -, -, -, -, hent⟩ := PState.repOk_parts hrok
  have hidsnd : (r0.2.entries.map (·.id)).Nodup := by
    rw [hids]; exact (hB.append_right H).nodup_iff.mpr (by rw [← hloc]; exact hnd)
  refine ⟨hidsnd, ?_⟩
  intro e he hK d hd
  obtain ⟨hcmd, hloce, hph3, h2, h1, h0⟩ := hent e he
  rw [hc] at hloce h2 h1 h0
  -- not class 0: a pre-acceptance or a proposal, with its own dependencies
  have hown : d ∈ depsIn (S.seqOf (S.loc r0.1 (recMaxC (recAcks reps)))) e.id := by
    by_cases hp2 : e.phase.toNat ≥ 2
    · exact absurd ⟨r0, hr0, e, he, rfl, by unfold okPhase; simp; omega⟩ hK
    · by_cases hp1 : e.phase.toNat = 1
      · rcases h1 hp1 with ⟨hL, -⟩ | hpre
        · exact absurd ⟨r0, hr0, e, he, rfl, by unfold okPhase; simp [hL, hp1]⟩ hK
        · obtain ⟨-, -, -, hD, -⟩ := hI.pre_ok _ _ _ _ hpre
          rw [← hD]; exact hd
      · exact h0 (by omega) d hd
  obtain ⟨hprec, cd, cy, hcd, hcy, hk⟩ := depsIn_loc S _ hnd (hI.loc_ok _ _).2.1 hown
  rw [hcmd] at hcy; cases hcy
  have hdloc : d ∈ S.loc r0.1 (recMaxC (recAcks reps)) := precedes_mem _ _ _ hprec
  have hmem : ∀ z ∈ S.loc r0.1 (recMaxC (recAcks reps)), z ∈ r0.2.entries.map (·.id) := by
    intro z hz; rw [hids]; rw [hloc] at hz
    rcases List.mem_append.mp hz with h | h
    · exact List.mem_append_left _ (hB.mem_iff.mpr h)
    · exact List.mem_append_right _ h
  have hdm := hmem d hdloc
  have hem := hmem e.id hloce
  refine ⟨fun h => precedes_irrefl _ _ (h ▸ hprec), ?_, ?_, ⟨cd, hcd, hk⟩⟩
  · obtain ⟨e', he', hid⟩ := List.mem_map.mp hdm; exact ⟨e', he', hid⟩
  · refine ⟨_, _, recPos_idx r0 d hdm, recPos_idx r0 e.id hem, ?_⟩
    apply precedes_lt_idx
    -- e.id is not a base command
    have heB : e.id ∉ S.base (recMaxC (recAcks reps)) := fun h => hK (K0_of_base hI hrep hr0 h)
    rw [hids, precedes_append_not B H d e.id (fun h => heB (hB.mem_iff.mp h))]
    rw [hloc, precedes_append_not _ H d e.id heB] at hprec
    rcases hprec with h | h
    · exact Or.inl (hB.mem_iff.mpr h)
    · exact Or.inr h
theorem R_sub {r0 : Nat × Report} {rs : List (Nat × Report)}
    (h : (recU (recAcks reps)).filter (fun a => a.1 ∈ AQ N (recMaxC (recAcks reps))) = r0 :: rs) :
    r0 ∈ recU (recAcks reps) ∧ r0.1 ∈ AQ N (recMaxC (recAcks reps)) ∧
      ∀ a ∈ rs, a ∈ recU (recAcks reps) ∧ a.1 ∈ AQ N (recMaxC (recAcks reps)) := by
  have hm : ∀ a ∈ r0 :: rs, a ∈ recU (recAcks reps) ∧ a.1 ∈ AQ N (recMaxC (recAcks reps)) := by
    intro a ha; rw [← h, List.mem_filter] at ha; simpa using ha
  exact ⟨(hm r0 (by simp)).1, (hm r0 (by simp)).2, fun a ha => hm a (by simp [ha])⟩

/-- The recovery of `reps` (a majority's reports for `b'`) as a context. -/
noncomputable def mkCtx : Ctx S N reps where
  acks := recAcks reps
  U := recU (recAcks reps)
  R := (recU (recAcks reps)).filter (fun a => a.1 ∈ AQ N (recMaxC (recAcks reps)))
  oldL := leaderOf N (recMaxC (recAcks reps))
  leaderInU := (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps)))
  k1 := _
  k2 := _
  k3 := _
  k3b := _
  k4 := _
  ids := _
  ord := S.ord N (recMaxC (recAcks reps))
  hacks := rfl
  hU := rfl
  hL := rfl
  hlU := rfl
  hR := rfl
  h1 := rfl
  h2 := rfl
  h3 := rfl
  h3b := rfl
  hids := rfl
  h4 := rfl
  H := ⟨fun a ha e he hok => K0_dep hI hrep ha he hok, by
    intro _ r0 rs hR e he hK d hd
    obtain ⟨h1, h2, -, -⟩ := (R0_facts hI hrep (R_sub hI hrep hR).1).2 e he hK d hd
    exact ⟨h1, Or.inr h2⟩⟩
  reg := fun a ha e he => by
    obtain ⟨hc, hrok⟩ := U_rep hI hrep ha
    obtain ⟨-, -, -, -, -, -, -, -, hent⟩ := PState.repOk_parts hrok
    exact (hent e he).1
  ordNd := (hI.loc_ok _ _).1
  ordReg := (hI.loc_ok _ _).2.1
  k0 := fun a ha e he hok => K0_entry hI hrep ha he hok
  pos := by
    intro _ r0 rs hR
    obtain ⟨h1, h2⟩ := R0_facts hI hrep (R_sub hI hrep hR).1
    exact ⟨h1, fun e he hK d hd => let r := h2 e he hK d hd; ⟨r.2.2.1, r.2.2.2⟩⟩
  regA := fun a ha e he => by
    have ha' : a ∈ reps := List.mem_mergeSort.mp ha
    obtain ⟨-, -, -, -, -, -, -, -, hent⟩ := PState.repOk_parts (hI.rep_ok a.1 b' a.2 (hrep a ha'))
    exact (hent e he).1
  Gd := fun y => K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) y ∧
    ((recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps))) = false ∨
      S.lexec N (recMaxC (recAcks reps)) y)
  gK0 := fun _ h => h.1
  gall := fun hl _ hK => ⟨hK, Or.inl hl⟩
  gdeps := fun a ha e he hok hG d hd => by
    obtain ⟨-, hx⟩ := hG
    rcases hx with hl | hx
    · rcases (K0_dep hI hrep ha he hok d hd).2 with h | ⟨h, -⟩
      · exact ⟨h, Or.inl hl⟩
      · rw [hl] at h; simp at h
    · have hdl : S.lexec N (recMaxC (recAcks reps)) d :=
        PState.lexec_deps hI hx ((K0_entry hI hrep ha he hok).2.mem_iff.mp hd)
      refine ⟨?_, Or.inr hdl⟩
      by_cases hLU : ∃ a' ∈ recU (recAcks reps), a'.1 = leaderOf N (recMaxC (recAcks reps))
      · obtain ⟨a', ha', hal⟩ := hLU; exact K0_of_lexec hI hrep ha' hal hdl
      · rcases (K0_dep hI hrep ha he hok d hd).2 with h | ⟨h, -⟩
        · exact h
        · exfalso
          obtain ⟨a', ha', hal⟩ := List.any_eq_true.mp h
          exact hLU ⟨a', ha', by simpa using hal⟩

theorem mkCtx_ord : (mkCtx hI hrep).ord = S.ord N (recMaxC (recAcks reps)) := rfl
/-- The fast path's paths (F2's fix): a command `R[0]` reported before the fast-chosen `x`, of
its key, is before `x` in the leader's order. -/
theorem F2_fast {r0 : Nat × Report} (hr0 : r0 ∈ recU (recAcks reps)) {x : CmdId}
    (hxK : ¬ K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) x)
    (hxloc : x ∈ S.loc r0.1 (recMaxC (recAcks reps))) {PL : List CmdId}
    (hp0 : S.path r0.1 (recMaxC (recAcks reps)) x = some PL)
    (hpL : S.path (leaderOf N (recMaxC (recAcks reps))) (recMaxC (recAcks reps)) x = some PL)
    {z : CmdId} {pz px : Nat} (hz : recPos r0 z = some pz) (hx : recPos r0 x = some px) (hlt : pz < px)
    (hkey : ∃ cz cx, S.cmds z = some cz ∧ S.cmds x = some cx ∧ cz.key = cx.key) :
    precedes (S.ord N (recMaxC (recAcks reps))) z x := by
  obtain ⟨B, H, hids, hB, hloc, hnd⟩ := rep_structure hI hrep hr0
  obtain ⟨cz, cx, hcz, hcx, hk⟩ := hkey
  have hxB : x ∉ S.base (recMaxC (recAcks reps)) := fun h => hxK (K0_of_base hI hrep hr0 h)
  have hzx := recPos_lt hz hx hlt
  rw [hids, precedes_append_not B H z x (fun h => hxB (hB.mem_iff.mp h))] at hzx
  obtain ⟨T, hT⟩ := base_prefix_ord hI (recMaxC (recAcks reps))
  have hordnd := (hI.loc_ok (leaderOf N (recMaxC (recAcks reps))) (recMaxC (recAcks reps))).1
  rw [← hT, precedes_append_not _ T z x hxB]
  rcases hzx with h | h
  · exact Or.inl (hB.mem_iff.mp h)
  · right
    have hregH : ∀ y ∈ H, S.cmds y ≠ none := fun y hy =>
      (hI.loc_ok r0.1 _).2.1 y (by rw [hloc]; simp [hy])
    have hzk : z ∈ S.keyPrefix r0.1 (recMaxC (recAcks reps)) x :=
      (mem_keyPrefix S _ _ H hloc hregH x z cx cz hcx hcz).mpr (Or.inr ⟨h, hk⟩)
    obtain ⟨-, -, -, -, hall⟩ := hI.path_ok _ _ _ _ hp0
    have hzP := hall z hzk
    obtain ⟨-, -, -, hLP, -⟩ := hI.path_ok _ _ _ _ hpL
    rw [hLP rfl] at hzP
    have hlocL : S.loc (leaderOf N (recMaxC (recAcks reps))) (recMaxC (recAcks reps)) =
        S.base (recMaxC (recAcks reps)) ++ T := hT.symm
    have hregT : ∀ y ∈ T, S.cmds y ≠ none := fun y hy =>
      (hI.loc_ok _ _).2.1 y (by rw [hlocL]; simp [hy])
    rcases (mem_keyPrefix S _ _ T hlocL hregT x z cx cz hcx hcz).mp hzP with h' | ⟨h', -⟩
    · exact absurd (h' ▸ hz) (by rw [hx]; intro e; cases e; omega)
    · exact h'
/-- The fast path's dependencies: `R[0]`'s last put before the fast-chosen get `x` is the
leader's. -/
theorem F3_fast {r0 : Nat × Report} (hr0 : r0 ∈ recU (recAcks reps)) {x : CmdId}
    (hxK : ¬ K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) x)
    (hxord : x ∈ S.ord N (recMaxC (recAcks reps)))
    {D0 : List CmdId} (hpre : S.pre r0.1 (recMaxC (recAcks reps)) x = some D0)
    (hD : D0.Perm (depsIn (S.seqOf (S.ord N (recMaxC (recAcks reps)))) x))
    {cx : Cmd} (hcx : S.cmds x = some cx) (hg : cx.isGet = true) {p : CmdId}
    (hp : S.LastPut (S.ord N (recMaxC (recAcks reps))) x cx.key (some p))
    {z : CmdId} {pz px : Nat}
    (hzK : ¬ K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) z)
    (hz : recPos r0 z = some pz) (hx : recPos r0 x = some px) (hlt : pz < px)
    (hput : S.isPutOf cx.key z) (hne : z ≠ p) :
    ∃ pp, recPos r0 p = some pp ∧ pz < pp := by
  obtain ⟨B, H, hids, hB, hloc, hnd⟩ := rep_structure hI hrep hr0
  have hreg := (hI.loc_ok r0.1 (recMaxC (recAcks reps))).2.1
  have hzB : z ∉ S.base (recMaxC (recAcks reps)) := fun h => hzK (K0_of_base hI hrep hr0 h)
  -- p is R[0]'s dependency of x
  have hpd : p ∈ depsIn (S.seqOf (S.ord N (recMaxC (recAcks reps)))) x :=
    (mkCtx hI hrep).lastPut_dep hxord hcx hg hp
  obtain ⟨-, -, hxloc, hD0, -⟩ := hI.pre_ok _ _ _ _ hpre
  have hp0 : p ∈ depsIn (S.seqOf (S.loc r0.1 (recMaxC (recAcks reps)))) x := by
    rw [← hD0]; exact hD.mem_iff.mpr hpd
  -- the loc around x
  obtain ⟨A, A', hA⟩ := List.append_of_mem hxloc
  have hxA : x ∉ A := by intro h; rw [hA, List.nodup_append] at hnd; exact hnd.2.2 x h x (by simp) rfl
  have hregA : ∀ y ∈ A, S.cmds y ≠ none := fun y hy => hreg y (by rw [hA]; simp [hy])
  have hseq : S.seqOf (S.loc r0.1 (recMaxC (recAcks reps))) = S.seqOf A ++ (x, cx) :: S.seqOf A' := by
    rw [hA, PState.seqOf_append, PState.seqOf_cons S x A' cx hcx]
  have hxA' : x ∉ (S.seqOf A).map Prod.fst := by rw [Ctx.seqOf_fst A hregA]; exact hxA
  rw [hseq] at hp0
  have := depsIn_split (S.seqOf A) (S.seqOf A') (x, cx) hxA'
  simp only at this; rw [this, mem_lkDeps] at hp0
  obtain ⟨t1, q, t2, ht, hqp, hqk, hnoput, -⟩ := hp0
  -- z is before x at R[0], so before p
  have hzx := recPos_lt hz hx hlt
  have hxB : x ∉ S.base (recMaxC (recAcks reps)) := fun h => hxK (K0_of_base hI hrep hr0 h)
  rw [hids, precedes_append_not B H z x (fun h => hxB (hB.mem_iff.mp h))] at hzx
  have hzxH : precedes H z x := by
    rcases hzx with h | h
    · exact absurd (hB.mem_iff.mp h) hzB
    · exact h
  have hzxl : precedes (S.loc r0.1 (recMaxC (recAcks reps))) z x := by
    rw [hloc, precedes_append_not _ H z x hxB]; exact Or.inr hzxH
  have hzA : z ∈ A := by
    have : precedes (A ++ x :: A') z x := hA ▸ hzxl
    unfold precedes at this; rwa [takeWhile_split A A' x hxA] at this
  -- in R[0]'s order before x, after p, there is no put of the key: z is before p
  have hAfst : A = t1.map Prod.fst ++ q.1 :: t2.map Prod.fst := by
    rw [← Ctx.seqOf_fst A hregA, ht]; simp
  rw [hAfst] at hzA
  have hzt1 : z ∈ t1.map Prod.fst := by
    rcases List.mem_append.mp hzA with h | h
    · exact h
    · simp at h; rcases h with h | ⟨c', hc'⟩
      · exact absurd (h.trans hqp) hne
      · exfalso
        have hm : (z, c') ∈ S.seqOf A := by rw [ht]; simp [hc']
        obtain ⟨hcz', -⟩ := Ctx.mem_seqOf hm
        obtain ⟨cz, hcz, hkz, hpz⟩ := hput
        have hce : c' = cz := Option.some.inj (hcz'.symm.trans hcz)
        subst hce
        have := hnoput (z, c') hc' hkz
        simp [hpz] at this
  have hndA : A.Nodup := by rw [hA] at hnd; exact (List.nodup_append.mp hnd).1
  have hpt1 : q.1 ∉ t1.map Prod.fst := by
    rw [hAfst] at hndA; intro h; exact (List.nodup_append.mp hndA).2.2 q.1 h q.1 (by simp) rfl
  have hzpA : precedes A z p := by
    rw [hAfst, ← hqp]; exact precedes_split _ _ _ _ hpt1 hzt1
  have hpA : p ∈ A := by rw [hAfst, ← hqp]; simp
  have hzpl : precedes (S.loc r0.1 (recMaxC (recAcks reps))) z p := by
    rw [hA]; exact (Ctx.precedes_append_of_mem A (x :: A') z p hpA).mpr hzpA
  have hpB : p ∉ S.base (recMaxC (recAcks reps)) := by
    intro hpb
    rw [hloc] at hzpl
    exact hzB (precedes_mem _ _ _ ((Ctx.precedes_append_of_mem _ H z p hpb).mp hzpl))
  rw [hloc, precedes_append_not _ H z p hpB] at hzpl
  have hzpH : precedes H z p := by
    rcases hzpl with h | h
    · exact absurd h hzB
    · exact h
  have hzpi : precedes (r0.2.entries.map (·.id)) z p := by
    rw [hids, precedes_append_not B H z p (fun h => hpB (hB.mem_iff.mp h))]; exact Or.inr hzpH
  have hpm : p ∈ r0.2.entries.map (·.id) := by
    rw [hids]; apply List.mem_append_right
    have : p ∈ S.loc r0.1 (recMaxC (recAcks reps)) := by rw [hA]; simp [hpA]
    rw [hloc] at this; rcases List.mem_append.mp this with h | h
    · exact absurd h hpB
    · exact h
  refine ⟨_, recPos_idx r0 p hpm, ?_⟩
  have := precedes_lt_idx _ _ _ hzpi
  rw [recPos_idx r0 z (recPos_mem hz)] at hz; cases hz
  exact this
end derive


/-! ## Ballot safety -/

theorem nodup_map_eq {α β : Type} (f : α → β) (l : List α) (hnd : (l.map f).Nodup) (a b : α)
    (ha : a ∈ l) (hb : b ∈ l) (hab : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (hab ▸ List.mem_map.mpr ⟨b, hb, rfl⟩) hnd.1
    · exact absurd (hab.symm ▸ List.mem_map.mpr ⟨a, ha, rfl⟩) hnd.1
    · exact ih hnd.2 ha hb

theorem acks_mem {reps : List (Nat × Report)} {p : Nat × Report} (h : p ∈ reps) : p ∈ recAcks reps := by
  unfold recAcks; exact List.mem_mergeSort.mpr h

theorem U_of_max {reps : List (Nat × Report)} {p : Nat × Report} (h : p ∈ recAcks reps)
    (hc : p.2.cbal = recMaxC (recAcks reps)) : p ∈ recU (recAcks reps) := by
  unfold recU; rw [List.mem_filter]; exact ⟨h, by simp [hc]⟩

namespace PState
variable {S : PState} {N : Nat} {fr : Bool}

/-- A command of a prefix has the same result in the whole sequence. -/
theorem resultIn_prefix_of (hI : S.PInv N fr) (B O : List CmdId) (hB : B <+: O) (hnd : O.Nodup)
    (hreg : ∀ y ∈ O, S.cmds y ≠ none) (x : CmdId) (hx : x ∈ B) :
    resultIn (S.seqOf O) x = resultIn (S.seqOf B) x := by
  obtain ⟨T, rfl⟩ := hB
  have hndB : B.Nodup := (List.nodup_append.mp hnd).1
  have hregB : ∀ y ∈ B, S.cmds y ≠ none := fun y hy => hreg y (by simp [hy])
  obtain ⟨cx, hcx⟩ := Option.ne_none_iff_exists'.mp (hreg x (by simp [hx]))
  cases hg : cx.isGet
  · rw [Ctx.resultIn_nonget (S := S) _ hreg x cx (by simp [hx]) hcx hg,
      Ctx.resultIn_nonget (S := S) _ hregB x cx hx hcx hg]
  · obtain ⟨p, hp⟩ := Ctx.lastPut_exists (S := S) B hndB x cx.key
    rw [S.resultIn_lastPut B hndB hregB x cx hx hcx p hp]
    have hp' : S.LastPut (B ++ T) x cx.key p := by
      cases p with
      | none => intro y hy; exact hp y ((Ctx.precedes_append_of_mem B T y x hx).mp hy)
      | some p =>
        obtain ⟨h1, h2, h3⟩ := hp
        have hpB : p ∈ B := precedes_mem _ _ _ h1
        refine ⟨(Ctx.precedes_append_of_mem B T p x hx).mpr h1, h2, fun y hy hpy => ?_⟩
        rcases h3 y ((Ctx.precedes_append_of_mem B T y x hx).mp hy) hpy with h | h
        · exact Or.inl h
        · exact Or.inr ((Ctx.precedes_append_of_mem B T y p hpB).mpr h)
    rw [S.resultIn_lastPut (B ++ T) hnd hreg x cx (by simp [hx]) hcx p hp']

/-- `LastPut` in a prefix containing `x` is `LastPut` in the whole sequence. -/
theorem LastPut_append_iff (S : PState) (B T : List CmdId) (x : CmdId) (k : w64) (p : Option CmdId)
    (hx : x ∈ B) : S.LastPut B x k p ↔ S.LastPut (B ++ T) x k p := by
  cases p with
  | none =>
    constructor
    · intro hp y hy; exact hp y ((Ctx.precedes_append_of_mem B T y x hx).mp hy)
    · intro hp y hy; exact hp y ((Ctx.precedes_append_of_mem B T y x hx).mpr hy)
  | some p =>
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hpB : p ∈ B := precedes_mem _ _ _ h1
      refine ⟨(Ctx.precedes_append_of_mem B T p x hx).mpr h1, h2, fun y hy hpy => ?_⟩
      rcases h3 y ((Ctx.precedes_append_of_mem B T y x hx).mp hy) hpy with h | h
      · exact Or.inl h
      · exact Or.inr ((Ctx.precedes_append_of_mem B T y p hpB).mpr h)
    · rintro ⟨h1, h2, h3⟩
      have h1' := (Ctx.precedes_append_of_mem B T p x hx).mp h1
      have hpB : p ∈ B := precedes_mem _ _ _ h1'
      refine ⟨h1', h2, fun y hy hpy => ?_⟩
      rcases h3 y ((Ctx.precedes_append_of_mem B T y x hx).mpr hy) hpy with h | h
      · exact Or.inl h
      · exact Or.inr ((Ctx.precedes_append_of_mem B T y p hpB).mp h)

/-- **Ballot safety** (the client-level form; see `Model.lean`). -/
theorem ballot_safety_proof (hI : S.PInv N fr) : ∀ (b' b : Nat) (x : CmdId), b < b' →
    S.sync b' ≠ none → S.possiblyChosen N b x →
    x ∈ S.base b' ∧ resultIn (S.seqOf (S.base b')) x = resultIn (S.ordSeq N b) x ∧
    (∀ y, S.conflicts y x → precedes (S.base b') y x → precedes (S.ord N b) y x) ∧
    (∀ cx p, S.cmds x = some cx → cx.isGet = true → S.LastPut (S.ord N b) x cx.key p →
      S.LastPut (S.base b') x cx.key p) := by
  intro b'
  induction b' using Nat.strongRecOn with
  | ind b' IH =>
  intro b x hb hs hx
  obtain ⟨M, hM⟩ := Option.ne_none_iff_exists'.mp hs
  obtain ⟨hb'0, -, hbord, reps, hmaj, hrep, hMeq⟩ := hI.sync_ok b' M hM
  have hbase : S.base b' = syncOrder (recoverSync N reps) := by
    unfold PState.base; rw [hM, hMeq]; rfl
  rw [hbase]
  let C := mkCtx hI hrep
  obtain ⟨hxord, hchosen, hlx⟩ := hx
  have hN : 0 < N := by
    obtain ⟨-, hlt, hlen⟩ := hmaj
    cases hr : reps.map Prod.fst with
    | nil => rw [hr] at hlen; simp at hlen
    | cons r _ => have := hlt r (by rw [hr]; simp); omega
  -- a reporter in x's quorum, which acted in b
  obtain ⟨p, hp, hpq⟩ : ∃ p ∈ reps, (p.1 = leaderOf N b ∨ S.acc p.1 b x) ∨
      (p.1 ∈ AQ N b ∧ S.fastChosen N b x) := by
    rcases hchosen with ⟨Q, hQ, hQall⟩ | hfast
    · obtain ⟨r, hr1, hr2⟩ := majority_meet N _ Q hmaj hQ
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr1
      exact ⟨p, hp, Or.inl (hQall _ hr2)⟩
    · obtain ⟨r, hr1, hr2⟩ := majority_meet N _ _ hmaj (AQ_majority N b hN).1
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr1
      exact ⟨p, hp, Or.inr ⟨hr2, hfast⟩⟩
  have hacted : x ∈ S.loc p.1 b := by
    rcases hpq with (h | h) | ⟨h, hf⟩
    · rw [h]; exact hxord
    · exact (hI.acc_ok _ _ _ h).2.1
    · unfold PState.fastChosen at hf
      obtain ⟨PL, -, hall⟩ := hf
      by_cases hL : p.1 = leaderOf N b
      · rw [hL]; exact hxord
      · obtain ⟨D, hD, -⟩ := hall p.1 h hL
        exact (hI.pre_ok _ _ _ _ hD).2.2.1
  have hprok := hI.rep_ok p.1 b' p.2 (hrep p hp)
  obtain ⟨-, hplt, -, hnone, -⟩ := PState.repOk_parts hprok
  have hpc : b ≤ p.2.cbal := by
    apply Classical.byContradiction; intro h
    have := (hnone b x (by omega) hb).2.2.2
    rw [this] at hacted; simp at hacted
  have hcmax := cbal_le_max _ p (acks_mem hp)
  obtain ⟨a, ha, hac⟩ := max_attained (recAcks reps) (by
    intro h; have := acks_mem hp; rw [h] at this; simp at this)
  have haU : a ∈ recU (recAcks reps) := U_of_max ha hac
  obtain ⟨-, harok⟩ := U_rep hI hrep haU
  obtain ⟨-, halt, habase, -⟩ := PState.repOk_parts harok
  rw [hac] at halt habase
  by_cases hbc : b < recMaxC (recAcks reps)
  · -- a later MSync: by induction, x is one of its commands
    obtain ⟨Mc, hMc, -⟩ := habase (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := IH _ halt b x hbc (by rw [hMc]; simp) ⟨hxord, hchosen, hlx⟩
    have hG : C.Gd x := ⟨K0_of_base hI hrep haU h1, Or.inr (PState.lexec_of_base h1)⟩
    obtain ⟨g1, g2, g3⟩ := C.safe_sync (C.safe_gd hG)
    obtain ⟨T, hT⟩ := base_prefix_ord hI (recMaxC (recAcks reps))
    have hordnd := (hI.loc_ok (leaderOf N (recMaxC (recAcks reps))) (recMaxC (recAcks reps))).1
    have hordreg := (hI.loc_ok (leaderOf N (recMaxC (recAcks reps))) (recMaxC (recAcks reps))).2.1
    refine ⟨g1, ?_, ?_, ?_⟩
    · rw [g2, ← h2]
      exact resultIn_prefix_of hI _ _ ⟨T, hT⟩ hordnd hordreg x h1
    · intro y hy hyx
      apply h3 y hy
      have := g3 y hy hyx
      change precedes (S.ord N (recMaxC (recAcks reps))) y x at this
      rw [← hT] at this
      exact (Ctx.precedes_append_of_mem _ T y x h1).mp this
    · intro cx q hcx hg hq
      apply C.safe_sync_lastPut (C.safe_gd hG) cx q hcx hg
      change S.LastPut (S.ord N (recMaxC (recAcks reps))) x cx.key q
      rw [← hT]
      exact (LastPut_append_iff S _ T x cx.key q h1).mp (h4 cx q hcx hg hq)
  · have hcb : recMaxC (recAcks reps) = b := by omega
    subst hcb
    have hpU : p ∈ recU (recAcks reps) := U_of_max (acks_mem hp) (by omega)
    -- x is safe in this recovery
    have hsafe : C.Safe x := by
      by_cases hK : K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) x
      · exact C.safe_gd ⟨hK, Or.inr hlx⟩
      · rcases hpq with (h | h) | ⟨hpAQ, hf⟩
        · exact absurd (K0_of_lexec hI hrep hpU h hlx) hK
        · exact absurd (K0_of_acc hI hrep hpU (Or.inl h)) hK
        · -- the fast path: the old leader did not report, R[0] pre-accepted x as every
          -- reporter of the fast quorum did
          have hLU : (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps))) = false := by
            cases hany : (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps)))
            · rfl
            · exfalso
              obtain ⟨a', ha', hal⟩ := List.any_eq_true.mp hany
              simp at hal
              exact hK (K0_of_lexec hI hrep ha' hal hlx)
          have hpL : p.1 ≠ leaderOf N (recMaxC (recAcks reps)) := by
            intro h
            have : (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps))) = true :=
              List.any_eq_true.mpr ⟨p, hpU, by simpa using h⟩
            rw [hLU] at this; simp at this
          have hpR : p ∈ (recU (recAcks reps)).filter (fun a => a.1 ∈ AQ N (recMaxC (recAcks reps))) :=
            List.mem_filter.mpr ⟨hpU, by simp [hpAQ]⟩
          obtain ⟨r0, rs, hR0⟩ : ∃ r0 rs, (recU (recAcks reps)).filter
              (fun a => a.1 ∈ AQ N (recMaxC (recAcks reps))) = r0 :: rs := by
            cases hR : (recU (recAcks reps)).filter (fun a => a.1 ∈ AQ N (recMaxC (recAcks reps))) with
            | nil => rw [hR] at hpR; simp at hpR
            | cons r0 rs => exact ⟨r0, rs, rfl⟩
          obtain ⟨hr0U, hr0AQ, hrsU⟩ := R_sub hI hrep hR0
          have notL : ∀ a ∈ recU (recAcks reps), a.1 ≠ leaderOf N (recMaxC (recAcks reps)) := by
            intro a' ha' h
            have : (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps))) = true :=
              List.any_eq_true.mpr ⟨a', ha', by simpa using h⟩
            rw [hLU] at this
            simp at this
          have hf' := hf
          unfold PState.fastChosen at hf'
          obtain ⟨PL, hPL, hall⟩ := hf'
          -- a reporter of R: its entry of x is a pre-acceptance with the leader's dependencies
          have entry_of : ∀ a ∈ recU (recAcks reps), a.1 ∈ AQ N (recMaxC (recAcks reps)) →
              ∃ D, S.pre a.1 (recMaxC (recAcks reps)) x = some D ∧
                D.Perm (depsIn (S.ordSeq N (recMaxC (recAcks reps))) x) ∧
                S.path a.1 (recMaxC (recAcks reps)) x = some PL ∧
                ∃ e ∈ a.2.entries, e.id = x ∧ e.phase.toNat = 1 ∧ e.dep = D := by
            intro a' ha' haq
            obtain ⟨D, hD, hDp, hpth⟩ := hall a'.1 haq (notL a' ha')
            obtain ⟨hc', hrok'⟩ := U_rep hI hrep ha'
            obtain ⟨-, -, -, -, -, hpre', -, -, hent'⟩ := PState.repOk_parts hrok'
            rw [hc'] at hpre'
            obtain ⟨e, he, hid, hph⟩ := hpre' x D hD
            refine ⟨D, hD, hDp, hpth, e, he, hid, ?_⟩
            rcases hph with hph | hph
            · exfalso; apply hK
              have := (hent' e he).2.2.1
              exact ⟨a', ha', e, he, hid, by unfold okPhase; simp; omega⟩
            · exact hph
          obtain ⟨D0, hD0, hD0p, hpth0, e0, he0, he0id, he0ph, he0dep⟩ := entry_of r0 hr0U hr0AQ
          obtain ⟨hnd0, -⟩ := R0_facts hI hrep hr0U
          -- rule 2 keeps x
          have hk1 : (C.k1.get x) = none := by
            have := ((rule1_spec C.oldL C.U).2.2 x)
            cases h' : C.k1.get x with
            | none => rfl
            | some _ =>
              exfalso; apply hK
              have h'' : (C.k1.get x).isSome := by rw [h']; rfl
              rw [show C.k1 = rule1 C.oldL C.U from C.h1] at h''
              exact this.mp h''
          have hall2 : rs.all (fun a => a.2.entries.any (fun e' =>
              e'.id == e0.id && e'.phase.toNat == 1 && depEq e0.dep e'.dep)) = true := by
            rw [List.all_eq_true]; intro a' ha'
            obtain ⟨ha'U, ha'AQ⟩ := hrsU a' ha'
            obtain ⟨D, -, hDp, -, e', he', he'id, he'ph, he'dep⟩ := entry_of a' ha'U ha'AQ
            rw [List.any_eq_true]
            refine ⟨e', he', ?_⟩
            simp only [Bool.and_eq_true, beq_iff_eq]
            refine ⟨⟨he'id.trans he0id.symm, he'ph⟩, ?_⟩
            unfold depEq; rw [List.isPerm_iff, he0dep, he'dep]
            exact hD0p.trans hDp.symm
          have hS1 : Struct C.oldL C.U C.leaderInU C.R C.acks C.k1 := by
            have := Struct_rule1 C.oldL C.U C.leaderInU C.R C.acks; rw [← C.h1] at this; exact this
          obtain ⟨-, -, hkeep⟩ := rule2_spec C.oldL C.U C.leaderInU C.R C.acks C.k1 hS1
          have hk2 : (C.k2.get x).isSome := by
            rw [C.h2]
            have := hkeep hLU r0 rs hR0 e0 he0 he0ph (by rw [he0id]; exact hk1) hall2
            rw [he0id] at this; exact this
          have hkept : (C.k4.get x).isSome :=
            (C.graph.1.keys x).mpr (C.graph.2.2.2 x hk2)
          have hpx : ∃ px, recPos r0 x = some px := by
            obtain ⟨px, h'⟩ := Ctx.recPos_of_mem he0; rw [he0id] at h'; exact ⟨px, h'⟩
          obtain ⟨px, hpx⟩ := hpx
          refine C.safe_fast hLU hR0 hK hkept hxord ?_ ?_ ?_
          · intro e he hid
            have : e = e0 := nodup_map_eq (·.id) _ hnd0 e e0 he he0 (hid.trans he0id.symm)
            subst this; rw [he0dep]; exact hD0p
          · intro z pz px' hz hx' hlt hkey
            have hpLx := hPL
            exact F2_fast hI hrep hr0U hK (hI.pre_ok _ _ _ _ hD0).2.2.1 hpth0 hpLx hz hx' hlt hkey
          · intro cx p' hcx hg hp' z pz px' hzK hz hx' hlt hput hne
            exact F3_fast hI hrep hr0U hK hxord hD0 hD0p hcx hg hp' hzK hz hx' hlt hput hne
    obtain ⟨g1, g2, g3⟩ := C.safe_sync hsafe
    exact ⟨g1, g2, g3, fun cx q hcx hg hq => C.safe_sync_lastPut hsafe cx q hcx hg hq⟩

end PState

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
