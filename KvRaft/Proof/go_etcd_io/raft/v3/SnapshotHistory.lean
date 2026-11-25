-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/SnapshotHistory.lean` (etc/copy-part.py; rerun it, do not edit).
/-
A node records the term and highest restored snapshot index at a successful
restore or a Ready handout. Both coordinates are monotone. The persistent
observations let two clients compare those events even after the node advances.
-/
module

public import Perennial.Ghost.MonoList
public import KvRaft.Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

namespace Perennial.EtcdGrove

open Iris Iris.BI Iris.ProofMode

section
variable {GF : BundledGFunctors} [AllG GF]

/-- The node owns the append-only observations. The state parameters bound every
observation it has issued. -/
noncomputable def snapHistoryOwn (γ : GName) (term index : Nat) : IProp GF :=
  iprop(∃ (events : List (Nat × Nat)), monoListAuthOwn γ 1 events ∗
    ⌜∀ e ∈ events, e.1 ≤ term ∧ e.2 ≤ index⌝)

/-- A restore or Ready handout at the indicated point in this node's history. -/
noncomputable def snapHistoryMark (sn : StorNames) (term index : Nat) : IProp GF :=
  iprop(∃ (before : List (Nat × Nat)), monoListLbOwn sn.history (before ++ [(term, index)]) ∗
    ⌜∀ e ∈ before, e.1 ≤ term ∧ e.2 ≤ index⌝)

instance (sn : StorNames) (t i : Nat) : Persistent (snapHistoryMark (GF := GF) sn t i) := by
  unfold snapHistoryMark; infer_instance

theorem snapHistory_alloc : ⊢ |==> ∃ γ, snapHistoryOwn (GF := GF) γ 0 0 := by
  imod mono_list_own_alloc ([] : List (Nat × Nat)) with ⟨%γ, Ha, -⟩
  imodintro
  iexists γ
  unfold snapHistoryOwn
  iexists []
  iframe Ha
  ipureintro; simp

/-- Steps between observations can increase either upper bound. -/
theorem snapHistory_raise (γ : GName) (t i t' i' : Nat) (ht : t ≤ t') (hi : i ≤ i') :
    snapHistoryOwn (GF := GF) γ t i ⊢ snapHistoryOwn γ t' i' := by
  unfold snapHistoryOwn
  iintro ⟨%events, Ha, %h⟩
  iexists events
  iframe Ha
  ipureintro
  exact fun e he => ⟨Nat.le_trans (h e he).1 ht, Nat.le_trans (h e he).2 hi⟩

theorem snapHistory_record (sn : StorNames) (t i t' i' : Nat) (ht : t ≤ t') (hi : i ≤ i') :
    ⊢ snapHistoryOwn (GF := GF) sn.history t i ==∗ snapHistoryOwn sn.history t' i' ∗ snapHistoryMark sn t' i' := by
  unfold snapHistoryOwn snapHistoryMark
  iintro ⟨%events, Ha, %h⟩
  imod monoListAuthOwn_update (events ++ [(t', i')]) ⟨_, rfl⟩ $$ Ha with ⟨Ha, #Hlb⟩
  have hprev : ∀ e ∈ events, e.1 ≤ t' ∧ e.2 ≤ i' :=
    fun e he => ⟨Nat.le_trans (h e he).1 ht, Nat.le_trans (h e he).2 hi⟩
  imodintro
  isplitl [Ha]
  · iexists (events ++ [(t', i')])
    iframe Ha
    ipureintro
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hprev e he
    · obtain rfl := List.mem_singleton.1 he
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · iexists events
    iframe Hlb
    ipureintro; exact hprev

private theorem snapHistory_prefix {a b : List (Nat × Nat)} {t i u j : Nat}
    (hp : a ++ [(t, i)] <+: b ++ [(u, j)])
    (hb : ∀ e ∈ b, e.1 ≤ u ∧ e.2 ≤ j) : t ≤ u ∧ i ≤ j := by
  have hm : (t, i) ∈ b ++ [(u, j)] := hp.sublist.subset (by simp)
  rcases List.mem_append.1 hm with hm | hm
  · exact hb _ hm
  · have he : (t, i) = (u, j) := List.mem_singleton.1 hm
    cases he; exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- At send time the current node state bounds every restore observed so far. -/
theorem snapHistory_mark_bound (sn : StorNames) (t i tr ir : Nat) :
    ⊢ snapHistoryOwn (GF := GF) sn.history t i -∗ snapHistoryMark sn tr ir -∗
      snapHistoryOwn sn.history t i ∗ ⌜tr ≤ t ∧ ir ≤ i⌝ := by
  unfold snapHistoryOwn snapHistoryMark
  iintro ⟨%events, Ha, %hb⟩ ⟨%pre, #Hm, -⟩
  ihave %hp := mono_list_auth_lb_valid sn.history 1 _ _ $$ Ha Hm
  isplitl [Ha]
  · iexists events; iframe Ha; ipureintro; exact hb
  · ipureintro
    exact hb (tr, ir) (hp.2.sublist.subset (by simp))

/-- A restore in a strictly earlier term cannot be ahead of this Ready. This
compares observations on the node itself and is independent of apply scheduling. -/
theorem snapHistory_index_le (sn : StorNames) (tr ir t i : Nat) (ht : tr < t) :
    ⊢ snapHistoryMark (GF := GF) sn tr ir -∗ snapHistoryMark sn t i -∗ ⌜ir ≤ i⌝ := by
  unfold snapHistoryMark
  iintro ⟨%a, #Ha, %ha⟩ ⟨%b, #Hb, %hb⟩
  ihave %hp := mono_list_lb_valid sn.history _ _ $$ Ha Hb
  ipureintro
  rcases hp with h | h
  · exact (snapHistory_prefix h hb).2
  · have := (snapHistory_prefix h ha).1; omega

/-- The node records (index, 1) when it restores a snapshot and (commit, 0)
when it hands out a Ready. A subsequent restore has to be past every earlier
commit. The Ready's history therefore accounts for every local restore at a
snapshot index already committed in that Ready. -/
noncomputable def installHistoryOwn (γ : GName) (commit : Nat) (indices : List Nat) : IProp GF :=
  iprop(∃ es : List (Nat × Nat), monoListAuthOwn γ 1 es ∗
    ⌜(∀ e ∈ es, e.1 ≤ commit) ∧ (∀ i, (i, 1) ∈ es → i ∈ indices)⌝)

noncomputable def installSeen (γ : GName) (index : Nat) : IProp GF :=
  iprop(∃ es : List (Nat × Nat), monoListLbOwn γ (es ++ [(index, 1)]) ∗
    ⌜∀ e ∈ es, e.1 < index⌝)

noncomputable def installView (γ : GName) (commit : Nat) (indices : List Nat) : IProp GF :=
  iprop(∃ es : List (Nat × Nat), monoListLbOwn γ (es ++ [(commit, 0)]) ∗
    ⌜∀ i, (i, 1) ∈ es → i ∈ indices⌝)

instance (γ : GName) (i : Nat) : Persistent (installSeen (GF := GF) γ i) := by
  unfold installSeen; infer_instance

instance (γ : GName) (c : Nat) (ks : List Nat) : Persistent (installView (GF := GF) γ c ks) := by
  unfold installView; infer_instance

theorem installHistory_alloc : ⊢ |==> ∃ γ, installHistoryOwn (GF := GF) γ 0 [] := by
  imod mono_list_own_alloc ([] : List (Nat × Nat)) with ⟨%γ, Ha, -⟩
  imodintro; iexists γ; unfold installHistoryOwn
  iexists []; iframe Ha; ipureintro; simp

theorem installHistory_raise (γ : GName) {c c' : Nat} (ks : List Nat) (hc : c ≤ c') :
    installHistoryOwn (GF := GF) γ c ks ⊢ installHistoryOwn γ c' ks := by
  unfold installHistoryOwn
  iintro ⟨%es, Ha, %h⟩; iexists es; iframe Ha
  ipureintro; exact ⟨fun e he => Nat.le_trans (h.1 e he) hc, h.2⟩

theorem installHistory_restore (γ : GName) {c c' i : Nat} (ks : List Nat) (hgt : c < i) (hi : i ≤ c') :
    ⊢ installHistoryOwn (GF := GF) γ c ks ==∗ installHistoryOwn γ c' (ks ++ [i]) ∗ installSeen γ i := by
  unfold installHistoryOwn installSeen
  iintro ⟨%es, Ha, %h⟩
  imod monoListAuthOwn_update (es ++ [(i, 1)]) ⟨_, rfl⟩ $$ Ha with ⟨Ha, #Hlb⟩
  imodintro; isplitl [Ha]
  · iexists (es ++ [(i, 1)]); iframe Ha; ipureintro
    constructor
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact Nat.le_trans (h.1 e he) (Nat.le_trans (Nat.le_of_lt hgt) hi)
      · cases List.mem_singleton.1 he; exact hi
    · intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · exact List.mem_append_left _ (h.2 j hj)
      · cases List.mem_singleton.1 hj; simp
  · iexists es; iframe Hlb; ipureintro
    exact fun e he => Nat.lt_of_le_of_lt (h.1 e he) hgt

theorem installHistory_ready (γ : GName) (c : Nat) (ks : List Nat) :
    ⊢ installHistoryOwn (GF := GF) γ c ks ==∗ installHistoryOwn γ c ks ∗ installView γ c ks := by
  unfold installHistoryOwn installView
  iintro ⟨%es, Ha, %h⟩
  imod monoListAuthOwn_update (es ++ [(c, 0)]) ⟨_, rfl⟩ $$ Ha with ⟨Ha, #Hlb⟩
  imodintro; isplitl [Ha]
  · iexists (es ++ [(c, 0)]); iframe Ha; ipureintro
    constructor
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact h.1 e he
      · cases List.mem_singleton.1 he; exact Nat.le_refl _
    · intro i hi
      exact h.2 i ((List.mem_append.1 hi).resolve_right (by simp))
  · iexists es; iframe Hlb; ipureintro; exact h.2

theorem installSeen_mem (γ : GName) {c i : Nat} (ks : List Nat) (hi : i ≤ c) :
    ⊢ installView (GF := GF) γ c ks -∗ installSeen γ i -∗ ⌜i ∈ ks⌝ := by
  unfold installView installSeen
  iintro ⟨%a, #Ha, %ha⟩ ⟨%b, #Hb, %hb⟩
  ihave %hp := mono_list_lb_valid γ _ _ $$ Ha Hb
  ipureintro
  rcases hp with h | h
  · have hm : (c, 0) ∈ b ++ [(i, 1)] := h.sublist.subset (by simp)
    have ht := hb (c, 0) ((List.mem_append.1 hm).resolve_right (by simp))
    exact False.elim (Nat.not_lt_of_ge hi ht)
  · have hm : (i, 1) ∈ a ++ [(c, 0)] := h.sublist.subset (by simp)
    exact ha i ((List.mem_append.1 hm).resolve_right (by simp))

end
end Perennial.EtcdGrove
