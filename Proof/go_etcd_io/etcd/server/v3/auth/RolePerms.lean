/-
A role's permissions, purely (PR etcd#21845, `pr-verify/etcd-21845`): the model of a role's
`KeyPermission` list, the order the auth store keeps it in, and what granting a permission is
meant to do. Lean-first (no Rocq counterpart).

* **A permission** `PermM`: its `Key`, `RangeEnd` (bytes) and `PermType`.
* **Sorted by key** (`SortedByKey`): no permission's key is less than an earlier one's (Go's
  `bytes.Compare`, `go.GoStringLt`). `permSlice.Less` compares keys only, so permissions with one
  key and different range ends are in any order among themselves.
* **Granting `p`** (`GrantSpec ps ps' p`, what `RoleGrantPermission` is meant to do, from the PR's
  description): if the role holds a permission with `p`'s key *and* range end, the first such one
  takes `p`'s type and nothing else changes; otherwise `p` is added and the list is sorted again
  (a permutation of `ps ++ [p]`, sorted by key; `sort.Sort` is not stable).
* **What the role then grants** (`grantSpec_mem`): when no two permissions of the role have the same
  key and range end (`NoDupRanges`), the new list holds exactly the old permissions with another
  range than `p`'s, and `p`; `NoDupRanges` and `SortedByKey` are kept (`grantSpec_nodup`,
  `grantSpec_sorted`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.slices.SortBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

/-! ## Go's `<` on byte strings -/

theorem permKeyLt_irrefl (a : GoString) : ¬ go.GoStringLt a a := by
  induction a with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | cons h => exact ih h
    | rel h => exact Int.lt_irrefl _ h

theorem permKeyLt_trans {a b c : GoString} (h1 : go.GoStringLt a b) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  induction h1 generalizing c with
  | nil => cases h2 <;> exact List.Lex.nil
  | cons h ih =>
    cases h2 with
    | cons h' => exact List.Lex.cons (ih h')
    | rel h' => exact List.Lex.rel h'
  | rel h =>
    cases h2 with
    | cons _ => exact List.Lex.rel h
    | rel h' => exact List.Lex.rel (Int.lt_trans h h')

/-- Two strings neither less than the other are equal. -/
theorem permKeyLt_eq_of_not_lt {a b : GoString} (h1 : ¬ go.GoStringLt a b)
    (h2 : ¬ go.GoStringLt b a) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => exact absurd List.Lex.nil h1
  | cons x xs ih =>
    cases b with
    | nil => exact absurd List.Lex.nil h2
    | cons y ys =>
      have hxy : x = y := by
        apply BitVec.eq_of_toNat_eq
        have a1 : ¬ (uint.Z x < uint.Z y) := fun h => h1 (List.Lex.rel h)
        have a2 : ¬ (uint.Z y < uint.Z x) := fun h => h2 (List.Lex.rel h)
        simp only [uint.Z] at a1 a2
        omega
      subst hxy
      rw [ih (fun h => h1 (List.Lex.cons h)) (fun h => h2 (List.Lex.cons h))]

/-- Total: one of `a < b`, `a = b`, `b < a`. -/
theorem permKeyLt_total (a b : GoString) : go.GoStringLt a b ∨ a = b ∨ go.GoStringLt b a := by
  by_cases h1 : go.GoStringLt a b
  · exact Or.inl h1
  by_cases h2 : go.GoStringLt b a
  · exact Or.inr (Or.inr h2)
  exact Or.inr (Or.inl (permKeyLt_eq_of_not_lt h1 h2))

/-! ## Permissions -/

/-- A permission of a role: `Key`, `RangeEnd`, `PermType`. -/
structure PermM where
  key : List w8
  rangeEnd : List w8
  permType : w32

/-- `permSlice.Less`: by key. -/
def keyLt (a b : PermM) : Prop := go.GoStringLt a.key b.key

instance keyLt_dec (a b : PermM) : Decidable (keyLt a b) :=
  inferInstanceAs (Decidable (go.GoStringLt a.key b.key))

theorem keyLt_swo {E : Type} (f : E → PermM) :
    slices.StrictWeakOrder (fun a b : E => keyLt (f a) (f b)) where
  strict_weak_order_irrefl x := permKeyLt_irrefl _
  strict_weak_order_trans _ _ _ h1 h2 := permKeyLt_trans h1 h2
  strict_weak_order_equiv := {
    refl := fun _ => ⟨permKeyLt_irrefl _, permKeyLt_irrefl _⟩
    symm := fun h => ⟨h.2, h.1⟩
    trans := fun h1 h2 => by
      have e1 := permKeyLt_eq_of_not_lt h1.1 h1.2
      have e2 := permKeyLt_eq_of_not_lt h2.1 h2.2
      unfold keyLt
      rw [e1, e2]
      exact ⟨permKeyLt_irrefl _, permKeyLt_irrefl _⟩ }

/-- Sorted by key: no permission's key is less than an earlier one's. -/
def SortedByKey (ps : List PermM) : Prop :=
  ∀ (i j : Nat) (a b : PermM), ps[i]? = some a → ps[j]? = some b → i < j → ¬ keyLt b a

/-- `a` is a permission on the same range as `p` (key and range end). -/
def sameRange (a p : PermM) : Prop := a.key = p.key ∧ a.rangeEnd = p.rangeEnd

/-- No two permissions on the same range. -/
def NoDupRanges (ps : List PermM) : Prop :=
  ∀ (i j : Nat) (a b : PermM), ps[i]? = some a → ps[j]? = some b → sameRange a b → i = j

/-- **Granting `p`** (`RoleGrantPermission`'s intended effect on the role's permissions): the
first permission on `p`'s range takes `p`'s type (it becomes `p`: same key and range end), or,
if there is none, `p` is added and the list sorted by key. -/
def GrantSpec (ps ps' : List PermM) (p : PermM) : Prop :=
  (∃ (i : Nat) (q : PermM), ps[i]? = some q ∧ sameRange q p ∧
      (∀ (k : Nat) (q' : PermM), k < i → ps[k]? = some q' → ¬ sameRange q' p) ∧
      ps' = ps.set i p) ∨
  ((∀ q ∈ ps, ¬ sameRange q p) ∧ List.Perm ps' (ps ++ [p]) ∧ SortedByKey ps')

theorem grantSpec_sorted {ps ps' : List PermM} {p : PermM} (hs : SortedByKey ps)
    (hg : GrantSpec ps ps' p) : SortedByKey ps' := by
  rcases hg with ⟨i, q, hq, ⟨hk, _⟩, _, rfl⟩ | ⟨_, _, hs'⟩
  · intro a b x y ha hb hab
    -- the entry at `i` has `q`'s key
    have key_of : ∀ (n : Nat) (z : PermM), (ps.set i p)[n]? = some z →
        ∃ z', ps[n]? = some z' ∧ z.key = z'.key := by
      intro n z hz
      rw [List.getElem?_set] at hz
      by_cases hn : i = n
      · subst hn
        have hlt : i < ps.length := by
          rcases (List.getElem?_eq_some_iff.1 hq) with ⟨h, _⟩; exact h
        simp only [hlt] at hz
        injection hz with hz
        subst hz
        exact ⟨q, hq, hk.symm⟩
      · simp only [if_neg hn] at hz
        exact ⟨z, hz, rfl⟩
    obtain ⟨x', hx', ekx⟩ := key_of a x ha
    obtain ⟨y', hy', eky⟩ := key_of b y hb
    have := hs a b x' y' hx' hy' hab
    unfold keyLt at this ⊢
    rw [ekx, eky]; exact this
  · exact hs'

theorem sameRange_symm {a b : PermM} (h : sameRange a b) : sameRange b a := ⟨h.1.symm, h.2.symm⟩

theorem sameRange_trans {a b c : PermM} (h1 : sameRange a b) (h2 : sameRange b c) :
    sameRange a c := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem sameRange_refl (a : PermM) : sameRange a a := ⟨rfl, rfl⟩

/-- What a role holds after a grant, when it had no two permissions on one range: its old
permissions on other ranges, and `p`. -/
theorem grantSpec_mem {ps ps' : List PermM} {p : PermM} (hd : NoDupRanges ps)
    (hg : GrantSpec ps ps' p) (q : PermM) :
    q ∈ ps' ↔ (q ∈ ps ∧ ¬ sameRange q p) ∨ q = p := by
  rcases hg with ⟨i, q0, hq0, hr0, _, rfl⟩ | ⟨hnone, hperm, _⟩
  · have hlt : i < ps.length := by
      rcases (List.getElem?_eq_some_iff.1 hq0) with ⟨h, _⟩; exact h
    constructor
    · intro hm
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
      rw [List.getElem?_set] at hn
      by_cases hin : i = n
      · subst hin; simp only [hlt] at hn; injection hn with hn; exact Or.inr hn.symm
      · simp only [if_neg hin] at hn
        left
        refine ⟨List.mem_of_getElem? hn, fun hs => hin ?_⟩
        exact hd i n q0 q hq0 hn (sameRange_trans hr0 (sameRange_symm hs))
    · rintro (⟨hm, hns⟩ | rfl)
      · obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
        have hin : i ≠ n := by
          rintro rfl
          rw [hq0] at hn; injection hn with hn; subst hn; exact hns hr0
        apply List.mem_of_getElem? (i := n)
        rw [List.getElem?_set, if_neg hin]; exact hn
      · apply List.mem_of_getElem? (i := i)
        rw [List.getElem?_set, if_pos rfl]; simp [hlt]
  · rw [hperm.mem_iff, List.mem_append, List.mem_singleton]
    constructor
    · rintro (hm | rfl)
      · exact Or.inl ⟨hm, hnone q hm⟩
      · exact Or.inr rfl
    · rintro (⟨hm, _⟩ | rfl)
      · exact Or.inl hm
      · exact Or.inr rfl

theorem grantSpec_nodup {ps ps' : List PermM} {p : PermM} (hd : NoDupRanges ps)
    (hg : GrantSpec ps ps' p) : NoDupRanges ps' := by
  rcases hg with ⟨i, q0, hq0, hr0, _, rfl⟩ | ⟨hnone, hperm, _⟩
  · intro a b x y ha hb hxy
    rw [List.getElem?_set] at ha hb
    have hlt : i < ps.length := by
      rcases (List.getElem?_eq_some_iff.1 hq0) with ⟨h, _⟩; exact h
    by_cases hia : i = a
    · by_cases hib : i = b
      · omega
      · subst hia
        simp only [hlt] at ha; injection ha with ha; subst ha
        simp only [if_neg hib] at hb
        exact absurd (hd _ _ _ _ hq0 hb (sameRange_trans hr0 hxy)) hib
    · simp only [if_neg hia] at ha
      by_cases hib : i = b
      · subst hib
        simp only [hlt] at hb; injection hb with hb; subst hb
        exact absurd (hd _ _ _ _ hq0 ha (sameRange_trans hr0 (sameRange_symm hxy))) hia
      · simp only [if_neg hib] at hb
        exact hd _ _ _ _ ha hb hxy
  · -- a list has no two on one range iff it is pairwise on different ranges
    have nodup_iff : ∀ l : List PermM, NoDupRanges l ↔
        l.Pairwise (fun a b => ¬ sameRange a b) := by
      intro l
      rw [List.pairwise_iff_getElem]
      constructor
      · intro h a b ha hb hab hs
        have := h a b _ _ (List.getElem?_eq_getElem ha) (List.getElem?_eq_getElem hb) hs
        omega
      · intro h a b x y ha hb hs
        rcases List.getElem?_eq_some_iff.1 ha with ⟨ha', rfl⟩
        rcases List.getElem?_eq_some_iff.1 hb with ⟨hb', rfl⟩
        rcases Nat.lt_trichotomy a b with hab | hab | hab
        · exact absurd hs (h a b ha' hb' hab)
        · exact hab
        · exact absurd (sameRange_symm hs) (h b a hb' ha' hab)
    rw [nodup_iff] at hd ⊢
    have hd2 : (ps ++ [p]).Pairwise (fun a b => ¬ sameRange a b) := by
      rw [List.pairwise_append]
      refine ⟨hd, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      exact hnone a ha
    exact hperm.symm.pairwise hd2 (fun h hs => h (sameRange_symm hs))

/-! ## The PR's search, purely

`RoleGrantPermission` binary-searches the first permission whose key is not less than `p`'s
(`sort.Search`), then scans the permissions from there while their key is `p`'s for one whose
range end is `p`'s. In a list sorted by key, the scan sees every permission with `p`'s key. -/

/-- `sort.Search`'s predicate: the key at `i` is not less than `k` (`bytes.Compare(.., k) >= 0`). -/
def keyGe (ps : List PermM) (k : List w8) (i : Int) : Bool :=
  match ps[i.toNat]? with
  | some q => decide (¬ go.GoStringLt q.key k)
  | none => true

theorem keyGe_mono {ps : List PermM} (hs : SortedByKey ps) (k : List w8) :
    ∀ (i j : Int), 0 ≤ i ∧ i < j ∧ j < ps.length → keyGe ps k i = true → keyGe ps k j = true := by
  intro i j ⟨hi, hij, hj⟩ h
  unfold keyGe at h ⊢
  have hi' : i.toNat < ps.length := by omega
  have hj' : j.toNat < ps.length := by omega
  rw [List.getElem?_eq_getElem hi'] at h
  rw [List.getElem?_eq_getElem hj']
  simp only [decide_eq_true_eq] at h ⊢
  intro hlt
  have hno := hs i.toNat j.toNat _ _ (List.getElem?_eq_getElem hi') (List.getElem?_eq_getElem hj')
    (by omega)
  unfold keyLt at hno
  rcases permKeyLt_total ps[j.toNat].key ps[i.toNat].key with h1 | h1 | h1
  · exact hno h1
  · rw [← h1] at h; exact h hlt
  · exact h (permKeyLt_trans h1 hlt)

/-- What the scan leaves in `existing` (`e`): `-1` and no permission on `p`'s range, or the index
of the first one. -/
def ExistingOk (ps : List PermM) (p : PermM) (e : Int) : Prop :=
  (e = -1 ∧ ∀ q ∈ ps, ¬ sameRange q p) ∨
  (0 ≤ e ∧ ∃ q, ps[e.toNat]? = some q ∧ sameRange q p ∧
    ∀ (k : Nat) (q' : PermM), k < e.toNat → ps[k]? = some q' → ¬ sameRange q' p)

/-- The scan stopped at `iv` (the end, or a key other than `p`'s and not less than it) without
finding `p`'s range below `iv`: there is none. -/
theorem scan_none {ps : List PermM} {p : PermM} (hs : SortedByKey ps) (iv : Nat)
    (hbelow : ∀ (k : Nat) (q : PermM), k < iv → ps[k]? = some q → ¬ sameRange q p)
    (hstop : ps.length ≤ iv ∨
      ∃ q, ps[iv]? = some q ∧ ¬ go.GoStringLt q.key p.key ∧ q.key ≠ p.key) :
    ∀ q ∈ ps, ¬ sameRange q p := by
  intro q hq hsr
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hq
  have hkl : k < ps.length := (List.getElem?_eq_some_iff.1 hk).1
  by_cases hki : k < iv
  · exact hbelow k q hki hk hsr
  rcases hstop with hlen | ⟨q0, hq0, hnlt, hne⟩
  · omega
  have hgt : go.GoStringLt p.key q0.key := by
    rcases permKeyLt_total q0.key p.key with h | h | h
    · exact absurd h hnlt
    · exact absurd h hne
    · exact h
  by_cases hk0 : k = iv
  · subst hk0; rw [hq0] at hk; injection hk with hk; subst hk
    exact hne hsr.1
  · have hno := hs iv k q0 q hq0 hk (by omega)
    unfold keyLt at hno
    rw [hsr.1] at hno
    exact hno hgt

/-- Below the scan's position `iv`: keys less than `p`'s (below the search's `idx`), then `p`'s
key with other range ends; none on `p`'s range. -/
theorem scan_below {ps : List PermM} {p : PermM} {idx iv : Nat}
    (hbefore : ∀ (k : Nat) (q : PermM), k < idx → ps[k]? = some q → go.GoStringLt q.key p.key)
    (hmid : ∀ (k : Nat) (q : PermM), idx ≤ k → k < iv → ps[k]? = some q →
      q.key = p.key ∧ q.rangeEnd ≠ p.rangeEnd) :
    ∀ (k : Nat) (q : PermM), k < iv → ps[k]? = some q → ¬ sameRange q p := by
  intro k q hk hq hsr
  by_cases hki : k < idx
  · have := hbefore k q hki hq
    rw [hsr.1] at this
    exact permKeyLt_irrefl _ this
  · exact (hmid k q (by omega) hk hq).2 hsr.2

end auth
end EtcdGrove
end Perennial
