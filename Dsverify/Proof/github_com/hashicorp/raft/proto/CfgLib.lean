/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/CfgLib.lean (241f27e).
-/
/-
`proto` (stage 4, internal) — the library behind `Cfg.lean`: the latest configuration of a log
(`lastCfgIdx`) characterized (`IsLast`), and quorum meeting for adjacent configurations.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.LC

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ### `isCfgAt` -/

theorem isCfgAt_iff (L : RLog) (k : Nat) :
    isCfgAt L k = true ↔ ∃ e, ent L k = some e ∧ e.kind = kConfig := by
  unfold isCfgAt
  cases h : ent L k <;> simp

theorem isCfgAt_false_iff (L : RLog) (k : Nat) :
    isCfgAt L k = false ↔ ∀ e, ent L k = some e → e.kind ≠ kConfig := by
  unfold isCfgAt
  cases h : ent L k <;> simp

@[simp] theorem isCfgAt_zero (L : RLog) : isCfgAt L 0 = false := by simp [isCfgAt]

theorem isCfgAt_take (L : RLog) (n k : Nat) (h : k ≤ n) : isCfgAt (L.take n) k = isCfgAt L k := by
  simp [isCfgAt, ent_take L n k h]

theorem isCfgAt_le {L : RLog} {k : Nat} (h : isCfgAt L k = true) : 1 ≤ k ∧ k ≤ L.length := by
  obtain ⟨e, he, _⟩ := (isCfgAt_iff L k).mp h
  exact ent_le_length he

theorem isCfgAt_of_agree {A B : RLog} {n k : Nat} (h : agree A B n) (hk : k ≤ n) :
    isCfgAt A k = isCfgAt B k := by
  simp [isCfgAt, agree_ent h hk]

/-! ### `lastCfgIdx` characterized -/

/-- `r` is the last configuration index of `L` at or below `n` (`0` if none). -/
def IsLast (L : RLog) (n r : Nat) : Prop :=
  r ≤ n ∧ (r = 0 ∨ isCfgAt L r = true) ∧ ∀ k, r < k → k ≤ n → isCfgAt L k = false

theorem IsLast.unique {L : RLog} {n r r' : Nat} (h : IsLast L n r) (h' : IsLast L n r') : r = r' := by
  obtain ⟨a, b, c⟩ := h
  obtain ⟨a', b', c'⟩ := h'
  rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
  · rcases b' with b' | b'
    · omega
    · rw [c r' hlt a'] at b'; cases b'
  · exact heq
  · rcases b with b | b
    · omega
    · rw [c' r hgt a] at b; cases b

private theorem fold_step (L : RLog) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc k => if isCfgAt L k then k else acc) 0 =
      if isCfgAt L n then n else (List.range n).foldl (fun acc k => if isCfgAt L k then k else acc) 0 := by
  rw [List.range_succ, List.foldl_append]
  simp

private theorem fold_isLast (L : RLog) (n : Nat) :
    IsLast L n ((List.range (n + 1)).foldl (fun acc k => if isCfgAt L k then k else acc) 0) := by
  induction n with
  | zero =>
    rw [fold_step]
    simp [IsLast]
    intro k h1 h2; omega
  | succ n ih =>
    rw [fold_step]
    by_cases hc : isCfgAt L (n + 1) = true
    · rw [if_pos' hc]
      refine ⟨Nat.le_refl _, Or.inr hc, fun k h1 h2 => by omega⟩
    · rw [if_neg' hc]
      obtain ⟨a, b, c⟩ := ih
      refine ⟨by omega, b, fun k h1 h2 => ?_⟩
      by_cases hk : k = n + 1
      · subst hk; simpa using hc
      · exact c k h1 (by omega)

theorem lastCfgIdx_isLast (L : RLog) : IsLast L L.length (lastCfgIdx L) := fold_isLast L L.length

theorem lastCfgIdx_eq_of_isLast {L : RLog} {r : Nat} (h : IsLast L L.length r) : lastCfgIdx L = r :=
  (lastCfgIdx_isLast L).unique h

theorem IsLast.take {L : RLog} {n m r : Nat} (h : IsLast (L.take n) m r) (hm : m ≤ n) : IsLast L m r := by
  obtain ⟨a, b, c⟩ := h
  refine ⟨a, ?_, fun k h1 h2 => ?_⟩
  · rcases b with b | b
    · exact Or.inl b
    · rw [isCfgAt_take _ _ _ (by omega)] at b; exact Or.inr b
  · rw [← isCfgAt_take L n k (by omega)]; exact c k h1 h2

theorem IsLast.of_take {L : RLog} {n m r : Nat} (h : IsLast L m r) (hm : m ≤ n) : IsLast (L.take n) m r := by
  obtain ⟨a, b, c⟩ := h
  refine ⟨a, ?_, fun k h1 h2 => ?_⟩
  · rcases b with b | b
    · exact Or.inl b
    · rw [isCfgAt_take _ _ _ (by omega)]; exact Or.inr b
  · rw [isCfgAt_take L n k (by omega)]; exact c k h1 h2

/-- The latest configuration of `L.take n` (`n ≤ |L|`) is the last of `L` at or below `n`. -/
theorem lc_isLast (L : RLog) {n : Nat} (hn : n ≤ L.length) : IsLast L n (lastCfgIdx (L.take n)) := by
  have h := lastCfgIdx_isLast (L.take n)
  rw [List.length_take, Nat.min_eq_left hn] at h
  exact h.take (Nat.le_refl _)

theorem lc_eq_of_isLast {L : RLog} {n r : Nat} (hn : n ≤ L.length) (h : IsLast L n r) :
    lastCfgIdx (L.take n) = r := (lc_isLast L hn).unique h

theorem lc_le (L : RLog) (n : Nat) : lastCfgIdx (L.take n) ≤ n := by
  have := (lastCfgIdx_isLast (L.take n)).1
  simp at this; omega

theorem lc_cfg (L : RLog) (n : Nat) : lastCfgIdx (L.take n) = 0 ∨ isCfgAt L (lastCfgIdx (L.take n)) = true := by
  rcases (lastCfgIdx_isLast (L.take n)).2.1 with h | h
  · exact Or.inl h
  · rw [isCfgAt_take _ _ _ (lc_le L n)] at h; exact Or.inr h

theorem lastCfgIdx_cfg (L : RLog) : lastCfgIdx L = 0 ∨ isCfgAt L (lastCfgIdx L) = true :=
  (lastCfgIdx_isLast L).2.1

theorem lastCfgIdx_le (L : RLog) : lastCfgIdx L ≤ L.length := (lastCfgIdx_isLast L).1

theorem lc_length (L : RLog) : lastCfgIdx (L.take L.length) = lastCfgIdx L := by
  rw [List.take_length]

/-- No configuration in `(a, b]`: the same latest configuration at `a` and `b`. -/
theorem lc_noCfg {L : RLog} {a b : Nat} (hab : a ≤ b) (hb : b ≤ L.length)
    (h : ∀ k, a < k → k ≤ b → isCfgAt L k = false) :
    lastCfgIdx (L.take a) = lastCfgIdx (L.take b) := by
  have ha := lc_isLast L (Nat.le_trans hab hb)
  symm
  apply lc_eq_of_isLast hb
  obtain ⟨x, y, z⟩ := ha
  refine ⟨by omega, y, fun k h1 h2 => ?_⟩
  by_cases hk : k ≤ a
  · exact z k h1 hk
  · exact h k (by omega) h2

/-- The latest configuration at `b` is also the latest at any `a` between it and `b`. -/
theorem lc_between {L : RLog} {a b : Nat} (hab : a ≤ b) (hb : b ≤ L.length)
    (h : lastCfgIdx (L.take b) ≤ a) : lastCfgIdx (L.take a) = lastCfgIdx (L.take b) := by
  apply lc_eq_of_isLast (Nat.le_trans hab hb)
  obtain ⟨x, y, z⟩ := lc_isLast L hb
  exact ⟨h, y, fun k h1 h2 => z k h1 (by omega)⟩

theorem lc_self {L : RLog} {a : Nat} (ha : a ≤ L.length) (h : isCfgAt L a = true) :
    lastCfgIdx (L.take a) = a :=
  lc_eq_of_isLast ha ⟨Nat.le_refl _, Or.inr h, fun k h1 h2 => by omega⟩

theorem lc_take_of_agree {A B : RLog} {n : Nat} (h : agree A B n) :
    lastCfgIdx (A.take n) = lastCfgIdx (B.take n) := by
  rw [h.2.2]

theorem lc_mono {L : RLog} {a b : Nat} (hab : a ≤ b) (hb : b ≤ L.length) :
    lastCfgIdx (L.take a) ≤ lastCfgIdx (L.take b) := by
  obtain ⟨x, y, z⟩ := lc_isLast L (Nat.le_trans hab hb)
  obtain ⟨x', y', z'⟩ := lc_isLast L hb
  apply Classical.byContradiction
  intro hn
  rcases y with y | y
  · omega
  · rw [z' _ (by omega) (by omega)] at y; cases y

/-- The latest configuration of a log at or below a configuration-free stretch. -/
theorem lastCfgIdx_eq_lc {L : RLog} {a : Nat} (ha : a ≤ L.length)
    (h : ∀ k, a < k → k ≤ L.length → isCfgAt L k = false) :
    lastCfgIdx L = lastCfgIdx (L.take a) := by
  rw [← lc_length]; exact (lc_noCfg ha (Nat.le_refl _) h).symm

/-- `cfgAt` of a prefix. -/
theorem cfgAt_take (σ : PState) (L : RLog) {n p : Nat} (h : p ≤ n) :
    cfgAt σ (L.take n) p = cfgAt σ L p := by
  simp [cfgAt, cfgAtC, ent_take L n p h]

theorem cfgAt_agree (σ : PState) {A B : RLog} {n p : Nat} (h : agree A B n) (hp : p ≤ n) :
    cfgAt σ A p = cfgAt σ B p := by
  simp [cfgAt, cfgAtC, agree_ent h hp]

theorem cfgOf_take (σ : PState) (L : RLog) (n : Nat) :
    cfgOf σ (L.take n) = cfgAt σ L (lastCfgIdx (L.take n)) := by
  simp only [cfgOf, cfgOfC]
  exact cfgAt_take σ L (lc_le L n)

/-! ### Quorums -/

theorem not_quorum_nil (Q : List SID) : ¬ isQuorumOf [] Q := by
  intro ⟨_, hs, h⟩
  cases Q with
  | nil => simp at h
  | cons a _ => exact absurd (hs a (by simp)) (by simp)

theorem cfgMeet_nil_left (B : List SID) : cfgMeet [] B := by
  intro Q1 Q2 h1; exact absurd h1 (not_quorum_nil Q1)

theorem cfgMeet_nil_right (A : List SID) : cfgMeet A [] := by
  intro Q1 Q2 h1 h2; exact absurd h2 (not_quorum_nil Q2)

theorem cfgMeet_symm {A B : List SID} (h : cfgMeet A B) : cfgMeet B A := by
  intro Q1 Q2 h1 h2
  obtain ⟨j, a, b⟩ := h Q2 Q1 h2 h1
  exact ⟨j, b, a⟩

theorem cfgMeet_refl (A : List SID) : cfgMeet A A := fun _ _ h1 h2 => quorum_inter h1 h2

/-- The core counting: `B ⊆ A ∪ {x}` and `A ⊆ B`. -/
private theorem meet_sub {A B Q1 Q2 : List SID} {x : SID} (hA : A.Nodup) (hB : B.Nodup)
    (hsub : ∀ y ∈ B, y ∈ A ∨ y = x) (hsup : ∀ y ∈ A, y ∈ B)
    (h1 : isQuorumOf A Q1) (h2 : isQuorumOf B Q2) : ∃ j, j ∈ Q1 ∧ j ∈ Q2 := by
  apply Classical.byContradiction
  intro hn
  have hd : ∀ a, a ∈ Q1 → ∀ b, b ∈ Q2 → a ≠ b := by
    intro a ha b hb hab; subst hab; exact hn ⟨a, ha, hb⟩
  obtain ⟨q1n, q1s, q1l⟩ := h1
  obtain ⟨q2n, q2s, q2l⟩ := h2
  have hAB : A.length ≤ B.length := List.Nodup.length_le_of_subset hA hsup
  by_cases hx : x ∈ A
  · have hnd : (Q1 ++ Q2).Nodup := List.nodup_append.mpr ⟨q1n, q2n, hd⟩
    have hs : Q1 ++ Q2 ⊆ A := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact q1s y hy
      · rcases hsub y (q2s y hy) with h | h
        · exact h
        · subst h; exact hx
    have := List.Nodup.length_le_of_subset hnd hs
    simp only [List.length_append] at this
    omega
  · have hxA : (x :: A).Nodup := List.nodup_cons.mpr ⟨hx, hA⟩
    have hBx : (x :: A).length ≤ B.length := by
      apply List.Nodup.length_le_of_subset hxA
      intro y hy
      rcases List.mem_cons.mp hy with h | h
      · subst h
        -- `x ∈ B`: else `B ⊆ A`, `Q1`, `Q2` both in `A`
        apply Classical.byContradiction
        intro hxB
        have hnd : (Q1 ++ Q2).Nodup := List.nodup_append.mpr ⟨q1n, q2n, hd⟩
        have hs : Q1 ++ Q2 ⊆ A := by
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact q1s z hz
          · rcases hsub z (q2s z hz) with h | h
            · exact h
            · subst h; exact absurd (q2s _ hz) hxB
        have := List.Nodup.length_le_of_subset hnd hs
        simp only [List.length_append] at this
        omega
      · exact hsup y h
    simp only [List.length_cons] at hBx
    have hnd : (Q1 ++ Q2.erase x).Nodup :=
      List.nodup_append.mpr ⟨q1n, q2n.erase x, fun a ha b hb => hd a ha b (List.mem_of_mem_erase hb)⟩
    have hs : Q1 ++ Q2.erase x ⊆ A := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact q1s y hy
      · have hy' := (List.Nodup.mem_erase_iff q2n).mp hy
        rcases hsub y (q2s y hy'.2) with h | h
        · exact h
        · exact absurd h hy'.1
    have := List.Nodup.length_le_of_subset hnd hs
    simp only [List.length_append] at this
    have : Q2.length ≤ (Q2.erase x).length + 1 := by
      by_cases hxq : x ∈ Q2
      · rw [List.length_erase_of_mem hxq]
        have : 0 < Q2.length := List.length_pos_of_mem hxq
        omega
      · rw [List.erase_of_not_mem hxq]; omega
    omega

theorem cfgMeet_of_adj' {A B : List SID} (hA : A.Nodup) (hB : B.Nodup)
    (hAB : (∀ y, y ∈ A ↔ y ∈ B) ∨ adjV A B) : cfgMeet A B := by
  intro Q1 Q2 h1 h2
  rcases hAB with h | ⟨x, h | h⟩
  · exact meet_sub (x := []) hA hB (fun y hy => Or.inl ((h y).mpr hy)) (fun y hy => (h y).mp hy) h1 h2
  · exact meet_sub hA hB (fun y hy => (h y).mp hy) (fun y hy => (h y).mpr (Or.inl hy)) h1 h2
  · obtain ⟨j, a, b⟩ :=
      meet_sub hB hA (fun y hy => (h y).mp hy) (fun y hy => (h y).mpr (Or.inl hy)) h2 h1
    exact ⟨j, b, a⟩

/-! ### Configurations in history logs -/

section hist
variable {σ : PState} (hG : IGen σ) (hL : ILeaders σ) (hLo : ILogs σ)
include hG hL hLo

theorem cfgAt_valid {X : RLog} (hX : LMok σ X) {p : Nat} (hp : isCfgAt X p = true) :
    cfgValid σ.srvs (cfgAt σ X p) := by
  obtain ⟨e, he, hk⟩ := (isCfgAt_iff X p).mp hp
  obtain ⟨h1, h2⟩ := ent_le_length he
  have a := hX p h1 h2
  have he' : ent (σ.llog (termAt X p)) p = some e := by rw [← agree_ent a (Nat.le_refl _)]; exact he
  have := hLo.2.2.2.2 _ p e he' hk
  simpa [cfgAt, cfgAtC, he] using this

theorem cfgAt_nodup {X : RLog} (hX : LMok σ X) {p : Nat} (hp : p = 0 ∨ isCfgAt X p = true) :
    (cfgAt σ X p).Nodup := by
  rcases hp with hp | hp
  · subst hp; simp [cfgAt, cfgAtC]
  · exact (cfgAt_valid hG hL hLo hX hp).2.1

omit hLo in
theorem ent_one_g {X : RLog} (hX : LMok σ X) (h : 1 ≤ X.length) : ent X 1 = some σ.g := by
  have a := hX 1 (Nat.le_refl _) h
  rw [agree_ent a (Nat.le_refl _)]
  by_cases ht : termAt X 1 = 1
  · rw [ht, hG.2.2.2.2.1]; rfl
  · have hl := llog_leader hL ht (by have := a.2.1; omega)
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hl
    exact (hL.1 _ ℓ hℓ).2.2.2.2.1

omit hG hLo in
theorem own_term {t k : Nat} (hl : σ.leader t ≠ none) (h1 : σ.len0 t < k) (h2 : k ≤ (σ.llog t).length) :
    termAt (σ.llog t) k = t := by
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hl
  obtain ⟨e, he⟩ := ent_isSome _ k (by omega) h2
  rw [termAt_of_ent he]
  exact (hL.1 t ℓ hℓ).2.2.2.2.2.2.1 k e h1 he

omit hLo in
theorem LMok_le_last {X : RLog} (hX : LMok σ X) {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ X.length) :
    termAt X k ≤ lastTerm X :=
  LMok_term_mono hG hL hX h1 h2 (Nat.le_refl _)

/-- A configuration entry at `p ≥ 2` of a history log was appended by the leader of its term:
its adjacency to its parent and its R-commit (`ICfgR`), read on the history log. -/
theorem cfgR_hist (hR : ICfgR σ) {X : RLog} (hX : LMok σ X) {p : Nat} (hp : isCfgAt X p = true)
    (hp2 : 2 ≤ p) :
    ∃ e, ent X p = some e ∧ e.kind = kConfig ∧ σ.leader (termAt X p) ≠ none ∧
      agree X (σ.llog (termAt X p)) p ∧ σ.len0 (termAt X p) < p ∧
      adjV (cfgOf σ (X.take (p - 1))) (σ.cv e.data) ∧
      cfgMeet (cfgAt σ X (lastCfgIdx (X.take (p - 1)))) (cfgAt σ X p) ∧
      ∃ k pc q, σ.commits (termAt X p) k pc ∧ σ.len0 (termAt X p) < k ∧
        lastCfgIdx (X.take (p - 1)) ≤ k ∧ k ≤ q ∧ q < p ∧ cfgAdmAt σ (termAt X p) q pc := by
  obtain ⟨e, he, hk⟩ := (isCfgAt_iff X p).mp hp
  obtain ⟨h1, h2⟩ := ent_le_length he
  have a := hX p h1 h2
  have ht1 : termAt X p ≠ 1 := by
    intro h; have := a.2.1; rw [h, hG.2.2.2.2.1] at this; simp at this; omega
  have hl := llog_leader hL ht1 (by have := a.2.1; omega)
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hl
  have hown : σ.len0 (termAt X p) < p :=
    llog_own_gt_len0 hL hℓ h1 (agree_termAt a (Nat.le_refl _)).symm
  have he' : ent (σ.llog (termAt X p)) p = some e := by rw [← agree_ent a (Nat.le_refl _)]; exact he
  obtain ⟨hadj, k, pc, q, hc, hk1, hk2, hk3, hk4, hk5⟩ := hR _ p e hl hown he' hk
  have htk : (σ.llog (termAt X p)).take (p - 1) = X.take (p - 1) := (agree_mono a (by omega)).2.2.symm
  rw [htk] at hadj hk2
  refine ⟨e, he, hk, hl, a, hown, hadj, ?_, k, pc, q, hc, hk1, hk2, hk3, hk4, hk5⟩
  have hpar : cfgOf σ (X.take (p - 1)) = cfgAt σ X (lastCfgIdx (X.take (p - 1))) := cfgOf_take σ X _
  have hch : σ.cv e.data = cfgAt σ X p := by simp [cfgAt, cfgAtC, he]
  rw [hpar, hch] at hadj
  refine cfgMeet_of_adj' (cfgAt_nodup hG hL hLo hX (lc_cfg X _)) (cfgAt_nodup hG hL hLo hX (Or.inr hp))
    (Or.inr hadj)

omit hG hL hLo in
/-- The configuration an R-commit counts: the parent, or the grandparent in the window. -/
theorem pc_char {X : RLog} {t p k q pc : Nat} (a : agree X (σ.llog t) p)
    (hk2 : lastCfgIdx (X.take (p - 1)) ≤ k) (hk3 : k ≤ q) (hk4 : q < p) (hpc : cfgAdmAt σ t q pc) :
    pc = lastCfgIdx (X.take (p - 1)) ∨
      (σ.len0 t < lastCfgIdx (X.take (p - 1)) ∧
        pc = lastCfgIdx (X.take (lastCfgIdx (X.take (p - 1)) - 1))) := by
  have hpX := a.1
  have e1 : lastCfgIdx ((σ.llog t).take q) = lastCfgIdx (X.take (p - 1)) := by
    rw [← lc_take_of_agree (agree_mono a (by omega))]
    exact lc_between (by omega) (by omega) (by omega)
  have e2 : (σ.llog t).take (lastCfgIdx (X.take (p - 1)) - 1) =
      X.take (lastCfgIdx (X.take (p - 1)) - 1) := by
    have := lc_le X (p - 1)
    exact (agree_mono a (by omega)).2.2.symm
  unfold cfgAdmAt at hpc
  rw [e1, e2] at hpc
  exact hpc

end hist

/-- A least witness. -/
theorem exists_least {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hm : ∃ m, m < n ∧ P m
    · obtain ⟨m, h1, h2⟩ := hm; exact ih m h1 h2
    · exact ⟨n, hn, fun m h1 h2 => hm ⟨m, h1, h2⟩⟩

/-- The first configuration of `X` in `(a, b]`. -/
theorem first_cfg {X : RLog} {a b : Nat} (h : ∃ k, a < k ∧ k ≤ b ∧ isCfgAt X k = true) :
    ∃ f, a < f ∧ f ≤ b ∧ isCfgAt X f = true ∧ ∀ k, a < k → k < f → isCfgAt X k = false := by
  obtain ⟨f, ⟨h1, h2, h3⟩, hmin⟩ := exists_least h
  refine ⟨f, h1, h2, h3, fun k hk1 hk2 => ?_⟩
  cases hc : isCfgAt X k
  · rfl
  · exact absurd ⟨hk1, by omega, hc⟩ (hmin k hk2)

theorem cfgOf_nil (σ : PState) : cfgOf σ [] = [] := by
  simp [cfgOf, cfgOfC, cfgAtC, ent]

end proto
end github_com.hashicorp.raft
end Perennial
