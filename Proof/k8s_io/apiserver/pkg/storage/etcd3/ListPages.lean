/-
Lean-first (no Rocq counterpart).

# The pages of a list compose to the store's list (pure; stage 7e-2, `store.GetList`'s proof)

- `scopeL`, `fromL`: a list's scope in the store, and its part from a start key (`pageKvsL`'s);
- `fromL_kp`: from the prepared key, the whole scope; `fromL_next`: from a page's last key and
  `"\x00"` (`store.go:903`), the scope after the page (`goStringLt_append_zero`: the keys not below
  `a ++ "\x00"` are the keys above `a`);
- `chunkL_agree`: `chunkL` (the chunks' loop, stopping at `more`) and 7e-3a's `loop` agree on the
  items, the last key and `more`, so the pages' chunks give `kListL`'s answer (`LAgree`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.ListPage

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 40000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open k8s_etcd3.ListModel

section pure
variable [GooseExts] {Obj : Type}

/-- **A list's scope** in the store `s`, in key order. -/
def scopeL (s : KVStore) (kp : GoString) (recur : Bool) : List EtcdKv :=
  s.kvs.filter fun v => kInScope kp recur v.key

/-- **A list's scope from the key `st`** (`pageKvsL`'s). -/
def fromL (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) : List EtcdKv :=
  s.kvs.filter fun v => kInScope kp recur v.key && !decide (go.GoStringLt v.key st)

theorem pageKvsL_eq (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) (l : Nat) :
    pageKvsL s kp recur st l =
      (if l = 0 then fromL s kp recur st else (fromL s kp recur st).take l,
        (fromL s kp recur st).length) := rfl

theorem goStringLt_append_zero :
    ∀ (a k : GoString), ¬ go.GoStringLt k (a ++ [W8 0]) ↔ go.GoStringLt a k
  | [], [] => ⟨fun h => absurd (go.goStringLt_nil_cons _ _) h,
      fun h => absurd h (go.goStringLt_irrefl _)⟩
  | [], x :: xs => by
    refine ⟨fun _ => go.goStringLt_nil_cons _ _, fun _ h => ?_⟩
    rw [List.nil_append, go.goStringLt_cons_iff] at h
    rcases h with h | ⟨-, h⟩
    · have h0 : uint.Z (W8 0) = 0 := rfl
      have hx : 0 ≤ uint.Z x := by simp only [uint.Z]; omega
      omega
    · exact go.goStringLt_not_nil _ h
  | b :: bs, [] => ⟨fun h => absurd (go.goStringLt_nil_cons _ _) h,
      fun h => absurd h (go.goStringLt_not_nil _)⟩
  | b :: bs, x :: xs => by
    rw [List.cons_append, go.goStringLt_cons_iff, go.goStringLt_cons_iff]
    have ih := goStringLt_append_zero bs xs
    by_cases hxb : x = b
    · subst hxb
      simp only [Int.lt_irrefl, false_or, true_and]
      exact ih
    · have hne : uint.Z x ≠ uint.Z b := by
        intro h; apply hxb; apply BitVec.eq_of_toNat_eq; simp only [uint.Z] at h; omega
      have hbx : ¬ b = x := fun h => hxb h.symm
      simp only [hxb, hbx, false_and, or_false]
      omega

theorem fromL_kp (s : KVStore) (kp : GoString) (recur : Bool) :
    fromL s kp recur kp = scopeL s kp recur := by
  unfold fromL scopeL
  apply List.filter_congr
  intro v _
  cases hs : kInScope kp recur v.key
  · rfl
  · have : ¬ go.GoStringLt v.key kp := by
      unfold kInScope at hs
      split at hs
      · exact prefix_not_lt _ _ (of_decide_eq_true hs)
      · rw [of_decide_eq_true hs]; exact go.goStringLt_irrefl _
    simp [this]

theorem fromL_sorted (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) :
    (fromL s kp recur st).Pairwise etcdKvLess :=
  (KVStore.kvs_sorted s).sublist List.filter_sublist

theorem scopeL_sorted (s : KVStore) (kp : GoString) (recur : Bool) :
    (scopeL s kp recur).Pairwise etcdKvLess :=
  (KVStore.kvs_sorted s).sublist List.filter_sublist

/-- In a key-sorted list, the elements after the `m`-th are those above it. -/
theorem drop_eq_filter_gt (l : List EtcdKv) (hl : l.Pairwise etcdKvLess) (m : Nat) (hm0 : 0 < m)
    (hm : m ≤ l.length) :
    l.drop m = l.filter fun v => decide (go.GoStringLt (l[m - 1]'(by omega)).key v.key) := by
  have hp := hl
  rw [← List.take_append_drop m l, List.pairwise_append] at hp
  obtain ⟨-, -, hcross⟩ := hp
  have hlast : l[m - 1]'(by omega) ∈ l.take m := by
    rw [List.mem_iff_getElem]
    exact ⟨m - 1, by simp; omega, by simp⟩
  generalize hk : (l[m - 1]'(by omega)).key = k0 at hlast ⊢
  conv => rhs; rw [← List.take_append_drop m l]
  rw [List.filter_append]
  have h1 : (l.take m).filter (fun v => decide (go.GoStringLt k0 v.key)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro v hv hlt
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    rw [List.getElem_take] at hjv
    subst hjv
    have hjm : j < m := by simp at hj; omega
    rcases Nat.lt_or_ge j (m - 1) with h | h
    · have h2 := (List.pairwise_iff_getElem.1 hl) j (m - 1) (by omega) (by omega) h
      unfold etcdKvLess at h2
      rw [hk] at h2
      exact go.goStringLt_asymm h2 (of_decide_eq_true hlt)
    · have : j = m - 1 := by omega
      subst this
      rw [hk] at hlt
      exact go.goStringLt_irrefl _ (of_decide_eq_true hlt)
  have h2 : (l.drop m).filter (fun v => decide (go.GoStringLt k0 v.key)) = l.drop m := by
    rw [List.filter_eq_self]
    intro v hv
    have := hcross _ hlast v hv
    unfold etcdKvLess at this
    rw [hk] at this
    exact decide_eq_true this
  rw [h1, h2, List.nil_append]

/-- From a page's last key and `"\x00"`, the scope after the page. -/
theorem fromL_next (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) (m : Nat)
    (hm0 : 0 < m) (hm : m ≤ (fromL s kp recur st).length) :
    fromL s kp recur (((fromL s kp recur st)[m - 1]'(by omega)).key ++ [W8 0]) =
      (fromL s kp recur st).drop m := by
  rw [drop_eq_filter_gt _ (fromL_sorted s kp recur st) m hm0 hm]
  generalize hkv : (fromL s kp recur st)[m - 1]'(by omega) = kv
  have hkvm : kv ∈ fromL s kp recur st := by rw [← hkv]; exact List.getElem_mem _
  have hkvst : ¬ go.GoStringLt kv.key st := by
    unfold fromL at hkvm
    have := (List.mem_filter.1 hkvm).2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this.2
  unfold fromL
  rw [List.filter_filter]
  apply List.filter_congr
  intro v _
  have h1 := goStringLt_append_zero kv.key v.key
  generalize kInScope kp recur v.key = a
  by_cases hb : go.GoStringLt kv.key v.key
  · have hc : ¬ go.GoStringLt v.key st := fun h => hkvst (go.goStringLt_trans hb h)
    have hd : ¬ go.GoStringLt v.key (kv.key ++ [W8 0]) := h1.2 hb
    rw [decide_eq_false hc, decide_eq_false hd, decide_eq_true hb]
  · have hd : go.GoStringLt v.key (kv.key ++ [W8 0]) :=
      Decidable.of_not_not (fun h => hb (h1.1 h))
    rw [decide_eq_true hd, decide_eq_false hb]
    try (cases a <;> rfl)

/-! ## The chunks' loop and 7e-3a's loop -/

/-- Two loop states agree on what a list answers: the items, the last key and `more`. -/
def LAgree {α O : Type} (a b : LState α O) : Prop :=
  a.items = b.items ∧ a.last = b.last ∧ a.more = b.more

/-- `more` is set only when the items are full. -/
def LInv {α O : Type} (lim : Nat) (s : LState α O) : Prop :=
  s.more = true → 0 < lim ∧ lim ≤ s.items.length

theorem lstep_inv {α O : Type} (sel : O → Bool) (lim : Nat) (s : LState α O) (ko : List α × O)
    (h : LInv lim s) : LInv lim (lstep sel lim s ko) := by
  unfold LInv at h ⊢
  simp only [lstep]
  split
  · intro _; assumption
  · split
    · intro hm
      have := h hm
      simp only [List.length_cons]
      omega
    · exact h

theorem foldl_stuck {α O : Type} (sel : O → Bool) (lim : Nat) (hl : 0 < lim) :
    ∀ (l : List (List α × O)) (s : LState α O), lim ≤ s.items.length → s.more = true →
      LAgree (l.foldl (lstep sel lim) s) s
  | [], s, _, _ => ⟨rfl, rfl, rfl⟩
  | ko :: l, s, h, hm => by
    rw [List.foldl_cons]
    have hs : lstep sel lim s ko = { s with total := s.total + 1, more := true } := by
      simp only [lstep]; simp [hl, h]
    rw [hs]
    obtain ⟨h1, h2, h3⟩ := foldl_stuck sel lim hl l { s with total := s.total + 1, more := true }
      h rfl
    exact ⟨h1, h2, by rw [h3, hm]⟩

theorem chunkL_agree {α O : Type} (sel : O → Bool) (lim : Nat) :
    ∀ (l : List (List α × O)) (s : LState α O), LInv lim s →
      LAgree (l.foldl (lstep sel lim) s) (chunkL sel lim s l)
  | [], s, _ => ⟨rfl, rfl, rfl⟩
  | ko :: l, s, h => by
    cases hm : s.more
    · simp only [chunkL, hm, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
      exact chunkL_agree sel lim l _ (lstep_inv sel lim s ko h)
    · simp only [chunkL, hm, ↓reduceIte]
      obtain ⟨hl, hle⟩ := h hm
      exact foldl_stuck sel lim hl (ko :: l) s hle hm

/-- `kListL` is the loop on the decoded scope. -/
theorem kListL_eq (dec : Dec Obj) (sel : Obj → Bool) (lim : Nat) (kp : GoString) (recur : Bool)
    (s : KVStore) :
    kListL dec sel lim kp recur s =
      loop (fun x => sel x.1) lim (decodedL dec (scopeL s kp recur)) := rfl

theorem kListL_agree (dec : Dec Obj) (sel : Obj → Bool) (lim : Nat) (kp : GoString) (recur : Bool)
    (s : KVStore) :
    LAgree (kListL dec sel lim kp recur s)
      (chunkL (fun x => sel x.1) lim ⟨[], none, false, 0⟩ (decodedL dec (scopeL s kp recur))) :=
  chunkL_agree _ _ _ _ (fun h => by cases h)

theorem decodedL_length (dec : Dec Obj) :
    ∀ (l : List EtcdKv), (∀ kv ∈ l, dec kv.value ≠ none) → (decodedL dec l).length = l.length
  | [], _ => rfl
  | kv :: l, h => by
    obtain ⟨d, hd⟩ : ∃ d, dec kv.value = some d := Option.ne_none_iff_exists'.1 (h kv (by simp))
    simp only [decodedL, List.filterMap_cons, hd, Option.map_some, List.length_cons]
    exact congrArg (· + 1) (decodedL_length dec l (fun kv' h' => h kv' (by simp [h'])))

theorem decodedL_append' (dec : Dec Obj) (a b : List EtcdKv) :
    decodedL dec (a ++ b) = decodedL dec a ++ decodedL dec b := by
  unfold decodedL; rw [List.filterMap_append]

/-- With every item selected and room for all, the chunk takes them all. -/
theorem chunkL_all {α O : Type} (sel : O → Bool) (lim : Nat) (hs : ∀ x, sel x = true) :
    ∀ (l : List (List α × O)) (s : LState α O), s.more = false →
      (lim = 0 ∨ s.items.length + l.length ≤ lim) →
      (chunkL sel lim s l).items.length = s.items.length + l.length ∧
        (chunkL sel lim s l).more = false
  | [], s, hm, _ => ⟨rfl, hm⟩
  | ko :: l, s, hm, h => by
    simp only [chunkL, hm, Bool.false_eq_true, ↓reduceIte]
    have hnf : ¬ (0 < lim ∧ lim ≤ s.items.length) := by
      simp only [List.length_cons] at h; omega
    have hst : lstep sel lim s ko =
        { s with total := s.total + 1, items := ko.2 :: s.items, last := some ko.1 } := by
      simp only [lstep]; rw [ite_eq_right_iff.2 (fun h => absurd h hnf)]; simp [hs]
    rw [hst]
    obtain ⟨h1, h2⟩ := chunkL_all sel lim hs l
      { s with total := s.total + 1, items := ko.2 :: s.items, last := some ko.1 } hm
      (by simp only [List.length_cons] at h ⊢; omega)
    refine ⟨?_, h2⟩
    rw [h1]; simp only [List.length_cons]; omega

/-! ## A page of the scope, and the list at a `break` -/

/-- A page's key-values are a prefix of the scope from its start, the count all of it. -/
theorem pageKvsL_prefix (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) (l : Nat) :
    fromL s kp recur st = (pageKvsL s kp recur st l).1 ++
      (fromL s kp recur st).drop (pageKvsL s kp recur st l).1.length ∧
    (pageKvsL s kp recur st l).2 = (fromL s kp recur st).length := by
  refine ⟨?_, rfl⟩
  rw [pageKvsL_eq]
  by_cases hl : l = 0
  · simp [hl]
  · simp only [hl, ↓reduceIte]
    rw [List.length_take]
    by_cases h : l ≤ (fromL s kp recur st).length
    · rw [Nat.min_eq_left h, List.take_append_drop]
    · rw [Nat.min_eq_right (by omega), List.drop_length, List.append_nil,
        List.take_of_length_le (by omega)]

/-- The loop state after a page that follows the first `m` key-values of the scope. -/
theorem chunkL_take_add {α : Type} (sel : Obj × α → Bool) (lim : Nat)
    (sc pg1 rest : List EtcdKv) (m : Nat) (h : sc.drop m = pg1 ++ rest)
    (f : List EtcdKv → List (GoString × (Obj × α))) (hf : ∀ a b, f (a ++ b) = f a ++ f b)
    (st0 : LState w8 (Obj × α)) :
    chunkL sel lim (chunkL sel lim st0 (f (sc.take m))) (f pg1) =
      chunkL sel lim st0 (f (sc.take (m + pg1.length))) := by
  rw [List.take_add, h, List.take_left' rfl, hf, chunkL_append]

theorem drop_add_page (sc pg1 rest : List EtcdKv) (m : Nat) (h : sc.drop m = pg1 ++ rest) :
    sc.drop (m + pg1.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left' rfl]

/-- **The list at a `break`**: after a page with the loop state `st'` on the scope read so far,
when the loop has more, or nothing is left, or the items are full, `kListL` answers `st'`'s items
and last key, with more iff `st'` has or something is left. -/
theorem kListL_final (dec : Dec Obj) (sel : Obj → Bool) (lim : Nat) (s : KVStore) (kp : GoString)
    (recur : Bool) (m : Nat) (pg1 rest : List EtcdKv)
    (hdrop : (scopeL s kp recur).drop m = pg1 ++ rest)
    (hdec : ∀ kv ∈ scopeL s kp recur, dec kv.value ≠ none)
    (st' : LState w8 (Obj × Nat))
    (hst' : st' = chunkL (fun x => sel x.1) lim ⟨[], none, false, 0⟩
      (decodedL dec ((scopeL s kp recur).take (m + pg1.length))))
    (hcase : st'.more = true ∨ rest = [] ∨ (0 < lim ∧ lim ≤ st'.items.length)) :
    (kListL dec sel lim kp recur s).items = st'.items ∧
      (kListL dec sel lim kp recur s).last = st'.last ∧
      (kListL dec sel lim kp recur s).more = decide (st'.more = true ∨ rest ≠ []) := by
  obtain ⟨h1, h2, h3⟩ := kListL_agree dec sel lim kp recur s
  have hsc : scopeL s kp recur = (scopeL s kp recur).take (m + pg1.length) ++ rest := by
    rw [← drop_add_page _ _ _ _ hdrop, List.take_append_drop]
  have heq : chunkL (fun x => sel x.1) lim ⟨[], none, false, 0⟩ (decodedL dec (scopeL s kp recur)) =
      chunkL (fun x => sel x.1) lim st' (decodedL dec rest) := by
    conv => lhs; rw [hsc]
    rw [decodedL_append', chunkL_append, ← hst']
  rw [h1, h2, h3, heq]
  rcases hcase with hm | hr | hf
  · rw [chunkL_more _ _ _ hm]
    simp [hm]
  · subst hr
    cases hm : st'.more <;> simp [decodedL, chunkL, hm]
  · cases rest with
    | nil => cases hm : st'.more <;> simp [decodedL, chunkL, hm]
    | cons x r =>
      have hx : x ∈ scopeL s kp recur := by
        have : x ∈ (scopeL s kp recur).drop m := by rw [hdrop]; simp
        exact List.mem_of_mem_drop this
      obtain ⟨d, hd⟩ : ∃ d, dec x.value = some d := Option.ne_none_iff_exists'.1 (hdec x hx)
      have hD : decodedL dec (x :: r) = (x.key, (d.1, sint.nat x.modRev)) :: decodedL dec r := by
        simp [decodedL, hd]
      cases hm : st'.more
      · rw [hD]
        simp only [chunkL, hm, Bool.false_eq_true, ↓reduceIte]
        have hl : lstep (fun x => sel x.1) lim st' (x.key, (d.1, sint.nat x.modRev)) =
            { st' with total := st'.total + 1, more := true } := by
          simp only [lstep]; simp [hf.1, hf.2]
        rw [hl, chunkL_more _ _ _ rfl]
        simp
      · rw [chunkL_more _ _ _ hm]
        simp [hm]

theorem kListL_total (dec : Dec Obj) (sel : Obj → Bool) (lim : Nat) (s : KVStore) (kp : GoString)
    (recur : Bool) (hdec : ∀ kv ∈ scopeL s kp recur, dec kv.value ≠ none) :
    (kListL dec sel lim kp recur s).total = (scopeL s kp recur).length := by
  rw [kListL_eq, loop_total, decodedL_length _ _ hdec]

theorem scopeL_prefix (s : KVStore) (kp : GoString) (recur : Bool) (kv : EtcdKv)
    (h : kv ∈ scopeL s kp recur) : kp <+: kv.key := by
  have := (List.mem_filter.1 h).2
  unfold kInScope at this
  split at this
  · exact of_decide_eq_true this
  · rw [of_decide_eq_true this]; exact List.prefix_refl _

theorem prepareKeyM_ne_nil (rp key k : GoString) (r : Bool) (h : prepareKeyM rp key r = some k) :
    k ≠ [] := by
  unfold prepareKeyM at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i h3
  split at h
  · simp at h
    rw [← h.2]; simp
  · simp at h
    rw [← h.2]; intro he; exact h3 (Or.inl he)

/-- **The first page with every item selected**: if it has more (it is then the limit's), the
items are full after it. -/
theorem page0_full (dec : Dec Obj) (sel : Obj → Bool) (hs : ∀ o, sel o = true) (lim : Nat)
    (F pg1 : List EtcdKv) (hdec : ∀ kv ∈ F, dec kv.value ≠ none)
    (hpg1 : pg1 = if lim = 0 then F else F.take lim) (hmore : pg1.length < F.length) :
    0 < lim ∧ lim ≤ (chunkL (fun x => sel x.1) lim ⟨[], none, false, 0⟩
      (decodedL dec pg1)).items.length := by
  have hl0 : lim ≠ 0 := by intro h; rw [h] at hpg1; simp at hpg1; rw [hpg1] at hmore; omega
  rw [ite_eq_right_iff.2 (fun h => absurd h hl0)] at hpg1
  have hlen : pg1.length = lim := by rw [hpg1, List.length_take]; rw [hpg1] at hmore; simp at hmore; omega
  have hd : (decodedL dec pg1).length = lim := by
    rw [decodedL_length _ _ (fun kv h => hdec kv (by rw [hpg1] at h; exact List.mem_of_mem_take h)),
      hlen]
  obtain ⟨h1, -⟩ := chunkL_all (fun x : Obj × Nat => sel x.1) lim (fun x => hs x.1)
    (decodedL dec pg1) (⟨[], none, false, 0⟩ : LState w8 (Obj × Nat)) rfl (Or.inr (by simp [hd]))
  refine ⟨by omega, ?_⟩
  rw [h1]; simp [hd]

/-- A page with more than it read is not empty. -/
theorem pageKvsL_more_ne (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) (l : Nat)
    (h : (pageKvsL s kp recur st l).1.length < (pageKvsL s kp recur st l).2) :
    (pageKvsL s kp recur st l).1 ≠ [] := by
  rw [pageKvsL_eq] at h ⊢
  by_cases hl : l = 0
  · simp [hl] at h
  · simp only [hl, ↓reduceIte, List.length_take] at h ⊢
    intro he
    have := congrArg List.length he
    simp only [List.length_take, List.length_nil] at this
    omega

end pure

end k8s
end EtcdGrove
end Perennial
