/-
**`fieldpath`'s tries, proved facts** (the representation of `Set`, `SetNodeMap`): a canonical
trie's paths as a list, a node list as pairs (path element, set of paths below it), and the views
of `isSet`/`isNodesV` the trie operations' proofs work at: a set is its members (`PathSet.tops`)
and its children (`PathSet.deep`), the children a sorted list of (element, `isSet`) nodes.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
public import Perennial.Proof.sort.FindBasics
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpC

/-! ## A trie's paths as a list -/

mutual
/-- The paths of a trie, listed. -/
def pathList : Trie → List Path
  | .mk ms cs => ms.map (fun e => [e]) ++ pathListC cs
/-- The paths below a list of children, listed. -/
def pathListC : List (PE × Trie) → List Path
  | [] => []
  | (e, t) :: cs => (pathList t).map (e :: ·) ++ pathListC cs
end

mutual
theorem mem_pathList : ∀ (t : Trie) (q : Path), q ∈ pathList t ↔ Trie.paths t q
  | .mk ms cs, q => by
    simp only [pathList, Trie.paths, List.mem_append, List.mem_map, mem_pathListC cs q]
    constructor
    · rintro (⟨e, he, rfl⟩ | h)
      · exact Or.inl ⟨e, rfl, he⟩
      · exact Or.inr h
    · rintro (⟨e, rfl, he⟩ | h)
      · exact Or.inl ⟨e, he, rfl⟩
      · exact Or.inr h
theorem mem_pathListC : ∀ (cs : List (PE × Trie)) (q : Path), q ∈ pathListC cs ↔ Trie.pathsC cs q
  | [], q => by simp [pathListC, Trie.pathsC]
  | (e, t) :: cs, q => by
    simp only [pathListC, Trie.pathsC, List.mem_append, List.mem_map, mem_pathListC cs q]
    constructor
    · rintro (⟨r, hr, rfl⟩ | h)
      · exact Or.inl ⟨r, rfl, (mem_pathList t r).1 hr⟩
      · exact Or.inr h
    · rintro (⟨r, rfl, hr⟩ | h)
      · exact Or.inl ⟨r, (mem_pathList t r).2 hr, rfl⟩
      · exact Or.inr h
end

/-- The set of a trie's paths. -/
def tset (t : Trie) : PathSet := FSet.ofList (pathList t)

theorem mem_tset (t : Trie) (q : Path) : q ∈ tset t ↔ Trie.paths t q := by
  unfold tset; rw [FSet.mem_ofList', mem_pathList]

theorem pathsC_ne_nil : ∀ cs : List (PE × Trie), ¬ Trie.pathsC cs []
  | [] => by simp [Trie.pathsC]
  | (e, t) :: cs => by
    have := pathsC_ne_nil cs
    simp only [Trie.pathsC]
    simp [this]

theorem paths_ne_nil (t : Trie) : ¬ Trie.paths t [] := by
  cases t with
  | mk ms cs =>
    have := pathsC_ne_nil cs
    simp only [Trie.paths]
    simp [this]

/-! ## Node lists: (path element, the set of paths below it) -/

abbrev NL := List (PE × PathSet)

/-- The paths of a node list: `k :: r` for `r` in `k`'s set. -/
def nlPaths : NL → PathSet
  | [] => FSet.empty
  | (k, S) :: l => FSet.union (FSet.map (k :: ·) S) (nlPaths l)

theorem mem_nlPaths : ∀ (l : NL) (q : Path),
    q ∈ nlPaths l ↔ ∃ k S r, (k, S) ∈ l ∧ r ∈ S ∧ q = k :: r
  | [], q => by simp [nlPaths, FSet.mem_empty]
  | (k, S) :: l, q => by
    simp only [nlPaths, FSet.mem_union', FSet.mem_map', mem_nlPaths l q, List.mem_cons,
      Prod.mk.injEq]
    constructor
    · rintro (⟨r, hr, rfl⟩ | ⟨k', S', r, h, hr, rfl⟩)
      · exact ⟨k, S, r, Or.inl ⟨rfl, rfl⟩, hr, rfl⟩
      · exact ⟨k', S', r, Or.inr h, hr, rfl⟩
    · rintro ⟨k', S', r, (⟨rfl, rfl⟩ | h), hr, rfl⟩
      · exact Or.inl ⟨r, hr, rfl⟩
      · exact Or.inr ⟨k', S', r, h, hr, rfl⟩

theorem mem_nlPaths_nil (q : Path) : q ∉ nlPaths [] := by simp [mem_nlPaths]

/-- A well-formed node list: keys strictly sorted and well-formed, every set non-empty, without
the empty path. -/
def NLok (l : NL) : Prop :=
  PE.Sorted (l.map (·.1)) ∧ ∀ k S, (k, S) ∈ l → k.wf = true ∧ (∃ q, q ∈ S) ∧ [] ∉ S

/-- A canonical trie's children as a node list. -/
def nlOf (cs : List (PE × Trie)) : NL := cs.map (fun p => (p.1, tset p.2))

theorem pathsC_nlOf : ∀ (cs : List (PE × Trie)) (q : Path),
    Trie.pathsC cs q ↔ q ∈ nlPaths (nlOf cs)
  | [], q => by simp [Trie.pathsC, nlOf, mem_nlPaths]
  | (e, t) :: cs, q => by
    have ih := pathsC_nlOf cs q
    simp only [nlOf] at ih
    simp only [Trie.pathsC, nlOf, List.map_cons, nlPaths, FSet.mem_union', FSet.mem_map', ih,
      mem_tset]
    constructor
    · rintro (⟨r, rfl, h⟩ | h)
      · exact Or.inl ⟨r, h, rfl⟩
      · exact Or.inr h
    · rintro (⟨r, h, rfl⟩ | h)
      · exact Or.inl ⟨r, rfl, h⟩
      · exact Or.inr h

theorem nlOf_keys (cs : List (PE × Trie)) : (nlOf cs).map (·.1) = cs.map (·.1) := by
  simp [nlOf]

theorem canonicalC_mem : ∀ (cs : List (PE × Trie)) (e : PE) (t : Trie), Trie.CanonicalC cs →
    (e, t) ∈ cs → Trie.Canonical t ∧ ∃ q, Trie.paths t q
  | [], _, _, _, h => by simp at h
  | (e', t') :: cs, e, t, hc, hm => by
    simp only [Trie.CanonicalC] at hc
    rcases List.mem_cons.1 hm with hm | hm
    · cases hm; exact ⟨hc.1, hc.2.1⟩
    · exact canonicalC_mem cs e t hc.2.2 hm

theorem tset_nonempty_of (t : Trie) (q : Path) (h : Trie.paths t q) : ∃ q, q ∈ tset t :=
  ⟨q, (mem_tset t q).2 h⟩

theorem pathsC_single : ∀ (cs : List (PE × Trie)) (e : PE), ¬ Trie.pathsC cs [e]
  | [], e => by simp [Trie.pathsC]
  | (e', t) :: cs, e => by
    have := pathsC_single cs e
    have := paths_ne_nil t
    simp only [Trie.pathsC]
    simp_all

theorem pathsC_len : ∀ (cs : List (PE × Trie)) (q : Path), Trie.pathsC cs q → 2 ≤ q.length
  | [], q, h => by simp [Trie.pathsC] at h
  | (e', t) :: cs, q, h => by
    simp only [Trie.pathsC] at h
    rcases h with ⟨r, rfl, hr⟩ | h
    · cases r with
      | nil => exact absurd hr (paths_ne_nil t)
      | cons _ _ => simp
    · exact pathsC_len cs q h

/-- A canonical trie's paths: its members' one-element paths and its children's. -/
theorem paths_mk (ms : List PE) (cs : List (PE × Trie)) (q : Path) :
    Trie.paths (.mk ms cs) q ↔ (∃ e, q = [e] ∧ e ∈ ms) ∨ Trie.pathsC cs q := by
  simp only [Trie.paths]

/-! ## Membership in the vocabulary's sets (the laws, as simp lemmas) -/

theorem mem_tops (S : PathSet) (e : PE) : e ∈ S.tops ↔ [e] ∈ S := PathSet_mem_tops_law_holds S e
theorem mem_deep (S : PathSet) (q : Path) : q ∈ S.deep ↔ q ∈ S ∧ 2 ≤ q.length :=
  PathSet_mem_deep_law_holds S q
theorem mem_heads (S : PathSet) (e : PE) : e ∈ S.heads ↔ ∃ q, q ≠ [] ∧ (e :: q) ∈ S :=
  PathSet_mem_heads_law_holds S e
theorem mem_under (S : PathSet) (e : PE) (q : Path) : q ∈ S.under e ↔ q ≠ [] ∧ (e :: q) ∈ S :=
  PathSet_mem_under_law_holds S e q
theorem mem_rdiff (A B : PathSet) (q : Path) :
    q ∈ PathSet.rdiff A B ↔ q ∈ A ∧ ∀ r ∈ q.nePrefixes, r ∉ B := PathSet_mem_rdiff_law_holds A B q
theorem mem_punion (A B : PathSet) (q : Path) : q ∈ PathSet.union A B ↔ q ∈ A ∨ q ∈ B :=
  FSet.mem_union' A B q
theorem mem_pinter (A B : PathSet) (q : Path) : q ∈ PathSet.inter A B ↔ q ∈ A ∧ q ∈ B :=
  FSet.mem_inter' A B q
theorem mem_pdiff (A B : PathSet) (q : Path) : q ∈ PathSet.diff A B ↔ q ∈ A ∧ q ∉ B :=
  FSet.mem_diff' A B q

/-! ## Emptiness -/

theorem isEmpty_iff (S : PathSet) : S.IsEmpty ↔ ∀ q, q ∉ S := FSet.isEmpty_iff' S

/-- A set without the empty path is empty iff its members and its children are. -/
theorem isEmpty_split (S : PathSet) (hne : [] ∉ S) :
    S.IsEmpty ↔ (∀ e, e ∉ S.tops) ∧ S.deep.IsEmpty := by
  rw [isEmpty_iff, isEmpty_iff]
  simp only [mem_tops, mem_deep]
  constructor
  · intro h; exact ⟨fun e => h [e], fun q hq => h q hq.1⟩
  · rintro ⟨h1, h2⟩ q hq
    match q with
    | [] => exact hne hq
    | [e] => exact h1 e hq
    | e :: e' :: r => exact h2 _ ⟨hq, by simp⟩

/-- A well-formed node list's paths are empty iff it has no node. -/
theorem nl_isEmpty (l : NL) (hl : NLok l) (D : PathSet) (hD : ∀ q, q ∈ D ↔ q ∈ nlPaths l) :
    D.IsEmpty ↔ l = [] := by
  rw [isEmpty_iff]
  constructor
  · intro h
    match l, hl with
    | [], _ => rfl
    | (k, S) :: l', hl =>
      obtain ⟨-, ⟨r, hr⟩, -⟩ := hl.2 k S (List.mem_cons_self ..)
      exact absurd ((hD _).2 ((mem_nlPaths _ _).2 ⟨k, S, r, List.mem_cons_self .., hr, rfl⟩))
        (h (k :: r))
  · rintro rfl q hq; exact mem_nlPaths_nil q ((hD q).1 hq)

/-- All elements well-formed. -/
abbrev AllWf (xs : List PE) : Prop := ∀ x ∈ xs, x.wf = true

theorem cmp_self (x : PE) (hx : x.wf = true) : PE.compare x x = 0 :=
  (PE_compare_eq_zero_law_holds x x hx hx).2 rfl

theorem lt_irrefl (x : PE) (hx : x.wf = true) : ¬ PE.lt x x := by
  unfold PE.lt; rw [cmp_self x hx]; decide

theorem sorted_nodup (xs : List PE) (hw : AllWf xs) (hs : PE.Sorted xs) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    unfold PE.Sorted at hs
    rw [List.pairwise_cons] at hs
    refine List.nodup_cons.2 ⟨fun hm => lt_irrefl x (hw x (by simp)) (hs.1 x hm), ?_⟩
    exact ih (fun y hy => hw y (by simp [hy])) hs.2

theorem hasCard_of_sorted (xs : List PE) (hw : AllWf xs) (hs : PE.Sorted xs) :
    (FSet.ofList xs).HasCard xs.length :=
  ⟨xs, sorted_nodup xs hw hs, rfl, rfl⟩

/-! ## Binary search over a sorted list -/

theorem lt_trans' {a b c : PE} (ha : a.wf = true) (hb : b.wf = true) (hc : c.wf = true) :
    PE.lt a b → PE.lt b c → PE.lt a c := PE_compare_trans_law_holds a b c ha hb hc

/-- Trichotomy. -/
theorem lt_total {a b : PE} (ha : a.wf = true) (hb : b.wf = true) :
    PE.lt a b ∨ a = b ∨ PE.lt b a := by
  unfold PE.lt
  have z := PE_compare_eq_zero_law_holds a b ha hb
  have an := PE_compare_antisymm_law_holds b a hb ha
  rcases Int.lt_trichotomy (PE.compare a b) 0 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (z.1 h))
  · exact Or.inr (Or.inr (an.2 h))

theorem lt_asymm {a b : PE} (ha : a.wf = true) (hb : b.wf = true) : PE.lt a b → ¬ PE.lt b a := by
  intro h1 h2
  exact lt_irrefl a ha (lt_trans' ha hb ha h1 h2)

theorem sorted_get {xs : List PE} (hs : PE.Sorted xs) {i j : Nat} {a b : PE}
    (hij : i < j) (ha : xs[i]? = some a) (hb : xs[j]? = some b) : PE.lt a b := by
  unfold PE.Sorted at hs
  rw [List.pairwise_iff_getElem] at hs
  have hi : i < xs.length := (List.getElem?_eq_some_iff.1 ha).1
  have hj : j < xs.length := (List.getElem?_eq_some_iff.1 hb).1
  have e1 := (List.getElem?_eq_some_iff.1 ha).2
  have e2 := (List.getElem?_eq_some_iff.1 hb).2
  have := hs i j hi hj hij
  rw [e1, e2] at this; exact this

/-- The binary search's index: the elements before it are below the target. -/
abbrev BsIdx (xs : List PE) (pe : PE) (i : Nat) : Prop :=
  i ≤ xs.length ∧ ∀ (k : Nat) (x : PE), xs[k]? = some x → (k < i ↔ PE.lt x pe)

theorem bs_found {xs : List PE} {pe : PE} {i : Nat} (hw : AllWf xs) (hp : pe.wf = true)
    (hs : PE.Sorted xs) (hb : BsIdx xs pe i) :
    (∃ x, xs[i]? = some x ∧ PE.compare x pe = 0) ↔ pe ∈ xs := by
  constructor
  · rintro ⟨x, hx, hc⟩
    have hxw := hw x (List.mem_of_getElem? hx)
    rw [(PE_compare_eq_zero_law_holds x pe hxw hp).1 hc] at hx
    exact List.mem_of_getElem? hx
  · intro hm
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hm
    have hj' : xs[j]? = some pe := by rw [List.getElem?_eq_getElem hj, hje]
    refine ⟨pe, ?_, cmp_self pe hp⟩
    rcases Nat.lt_trichotomy j i with h | h | h
    · exact absurd ((hb.2 j pe hj').1 h) (lt_irrefl pe hp)
    · rw [← h]; exact hj'
    · have hi : i < xs.length := by omega
      have hy : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
      have l1 := sorted_get hs h hy hj'
      have := (hb.2 i xs[i] hy).2 l1
      omega

theorem bs_take_lt {xs : List PE} {pe : PE} {i : Nat} (hb : BsIdx xs pe i) :
    ∀ a ∈ xs.take i, PE.lt a pe := by
  intro a ha
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem ha
  simp only [List.length_take] at hk
  have : xs[k]? = some a := by
    rw [← hke, List.getElem_take]; exact List.getElem?_eq_getElem (by omega)
  exact (hb.2 k a this).1 (by omega)

theorem bs_drop_nlt {xs : List PE} {pe : PE} {i : Nat} (hb : BsIdx xs pe i) :
    ∀ b ∈ xs.drop i, ¬ PE.lt b pe := by
  intro b hbm
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hbm
  simp only [List.length_drop] at hk
  have : xs[i + k]? = some b := by
    rw [← hke, List.getElem_drop]; exact List.getElem?_eq_getElem (by omega)
  intro hl
  have := (hb.2 (i + k) b this).2 hl
  omega

/-- Inserting the target at the search's index keeps the list sorted. -/
theorem bs_insert_sorted {xs : List PE} {pe : PE} {i : Nat} (hw : AllWf xs) (hp : pe.wf = true)
    (hs : PE.Sorted xs) (hb : BsIdx xs pe i) (hn : pe ∉ xs) :
    PE.Sorted (xs.take i ++ pe :: xs.drop i) := by
  have hs' := hs
  unfold PE.Sorted at hs' ⊢
  rw [← List.take_append_drop i xs, List.pairwise_append] at hs'
  rw [List.pairwise_append, List.pairwise_cons]
  have hdrop : ∀ b ∈ xs.drop i, PE.lt pe b := by
    intro b hbm
    have hbw := hw b (List.mem_of_mem_drop hbm)
    rcases lt_total hp hbw with h | h | h
    · exact h
    · subst h; exact absurd (List.mem_of_mem_drop hbm) hn
    · exact absurd h (bs_drop_nlt hb b hbm)
  refine ⟨hs'.1, ⟨hdrop, hs'.2.1⟩, ?_⟩
  intro a ha b hbm
  rcases List.mem_cons.1 hbm with rfl | hbm
  · exact bs_take_lt hb a ha
  · exact hs'.2.2 a ha b hbm

/-- The signs of `compare · pe` are non-decreasing along a sorted list. -/
theorem sorted_signum {xs : List PE} {pe : PE} (hw : AllWf xs) (hp : pe.wf = true)
    (hs : PE.Sorted xs) (k l : Nat) (a b : PE) (ha : xs[k]? = some a) (hb : xs[l]? = some b)
    (hkl : k < l) : sort.signum (PE.compare a pe) ≤ sort.signum (PE.compare b pe) := by
  have haw := hw a (List.mem_of_getElem? ha)
  have hbw := hw b (List.mem_of_getElem? hb)
  have hab := sorted_get hs hkl ha hb
  have za := PE_compare_eq_zero_law_holds a pe haw hp
  have zb := PE_compare_eq_zero_law_holds b pe hbw hp
  have key : PE.compare b pe ≤ 0 → PE.compare a pe < 0 := by
    intro hle
    rcases Int.lt_or_eq_of_le hle with h | h
    · exact lt_trans' haw hbw hp hab h
    · have hbe := zb.1 h; subst hbe; exact hab
  unfold sort.signum
  split <;> split <;> (try split) <;> (try split) <;> omega

/-- `slices.BinarySearchFunc`'s result over the Go elements, read over their models. -/
theorem bs_transfer {E : Type} (es : List E) (xs : List PE) (pe : PE) (m : E → PE)
    (hmd : ∀ (k : Nat) (a : E), es[k]? = some a → xs[k]? = some (m a))
    (hlen : es.length = xs.length) (i : Int) (found : Bool)
    (hi1 : 0 ≤ i ∧ i ≤ es.length)
    (hi2 : ∀ (k : Nat) (ek : E), es[k]? = some ek → ((k : Int) < i ↔ PE.compare (m ek) pe < 0))
    (hi3 : found = true ↔ ∃ ei, es[i.toNat]? = some ei ∧ PE.compare (m ei) pe = 0) :
    BsIdx xs pe i.toNat ∧ (found = true ↔ ∃ x, xs[i.toNat]? = some x ∧ PE.compare x pe = 0) := by
  have back : ∀ (k : Nat) (x : PE), xs[k]? = some x → ∃ a, es[k]? = some a ∧ m a = x := by
    intro k x hx
    have hk : k < es.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hx).1
    refine ⟨es[k], List.getElem?_eq_getElem hk, ?_⟩
    have := hmd k es[k] (List.getElem?_eq_getElem hk)
    rw [hx] at this; exact (Option.some.inj this).symm
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · intro k x hx
    obtain ⟨a, ha, rfl⟩ := back k x hx
    have := hi2 k a ha
    unfold PE.lt
    constructor
    · intro h; exact this.1 (by omega)
    · intro h; have := this.2 h; omega
  · rw [hi3]
    constructor
    · rintro ⟨a, ha, hc⟩; exact ⟨m a, hmd _ a ha, hc⟩
    · rintro ⟨x, hx, hc⟩
      obtain ⟨a, ha, rfl⟩ := back _ x hx
      exact ⟨a, ha, hc⟩

/-! ## The merge loops (`Union`, `Intersection`, `Difference`) -/

theorem take_succ' {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

theorem drop_cons' {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    xs.drop i = xs[i] :: xs.drop (i + 1) :=
  List.drop_eq_getElem_cons h

theorem sorted_drop_lt {xs : List PE} (hs : PE.Sorted xs) (i : Nat) (h : i < xs.length) :
    ∀ b ∈ xs.drop (i + 1), PE.lt xs[i] b := by
  have hs' := hs
  unfold PE.Sorted at hs'
  rw [← List.take_append_drop i xs, List.pairwise_append, drop_cons' xs i h,
    List.pairwise_cons] at hs'
  exact hs'.2.1.1

theorem mem_drop_of_succ {α : Type} {xs : List α} {i : Nat} (hi : i < xs.length) {b : α}
    (hb : b ∈ xs.drop (i + 1)) : b ∈ xs.drop i := by
  rw [drop_cons' xs i hi]; exact List.mem_cons_of_mem _ hb

/-- The merge's frontier: what was consumed is below what is left. -/
def Front (xs ys : List PE) (i j : Nat) : Prop :=
  ∀ a ∈ xs.take i ++ ys.take j, ∀ b ∈ xs.drop i ++ ys.drop j, PE.lt a b

theorem front_zero (xs ys : List PE) : Front xs ys 0 0 := by
  intro a ha; simp at ha

theorem front_step_x {xs ys : List PE} {i j : Nat} (hs : PE.Sorted xs) (hf : Front xs ys i j)
    (hi : i < xs.length) (hlt : ∀ b ∈ ys.drop j, PE.lt xs[i] b) : Front xs ys (i + 1) j := by
  intro a ha b hb
  rw [take_succ' xs i hi] at ha
  simp only [List.mem_append, List.mem_singleton] at ha hb
  rcases ha with (ha | rfl) | ha
  · refine hf a (by simp [ha]) b ?_
    rcases hb with hb | hb
    · exact List.mem_append.2 (Or.inl (mem_drop_of_succ hi hb))
    · exact List.mem_append.2 (Or.inr hb)
  · rcases hb with hb | hb
    · exact sorted_drop_lt hs i hi b hb
    · exact hlt b hb
  · refine hf a (by simp [ha]) b ?_
    rcases hb with hb | hb
    · exact List.mem_append.2 (Or.inl (mem_drop_of_succ hi hb))
    · exact List.mem_append.2 (Or.inr hb)

theorem front_step_y {xs ys : List PE} {i j : Nat} (hs : PE.Sorted ys) (hf : Front xs ys i j)
    (hj : j < ys.length) (hlt : ∀ b ∈ xs.drop i, PE.lt ys[j] b) : Front xs ys i (j + 1) := by
  intro a ha b hb
  rw [take_succ' ys j hj] at ha
  simp only [List.mem_append, List.mem_singleton] at ha hb
  rcases ha with ha | (ha | rfl)
  · refine hf a (by simp [ha]) b ?_
    rcases hb with hb | hb
    · exact List.mem_append.2 (Or.inl hb)
    · exact List.mem_append.2 (Or.inr (mem_drop_of_succ hj hb))
  · refine hf a (by simp [ha]) b ?_
    rcases hb with hb | hb
    · exact List.mem_append.2 (Or.inl hb)
    · exact List.mem_append.2 (Or.inr (mem_drop_of_succ hj hb))
  · rcases hb with hb | hb
    · exact hlt b hb
    · exact sorted_drop_lt hs j hj b hb

theorem front_step_eq {xs ys : List PE} {i j : Nat} (hsx : PE.Sorted xs) (hsy : PE.Sorted ys)
    (hf : Front xs ys i j) (hi : i < xs.length) (hj : j < ys.length) (he : xs[i] = ys[j]) :
    Front xs ys (i + 1) (j + 1) := by
  intro a ha b hb
  rw [take_succ' xs i hi, take_succ' ys j hj] at ha
  simp only [List.mem_append, List.mem_singleton] at ha hb
  have old : ∀ a, (a ∈ xs.take i ∨ a ∈ ys.take j) → PE.lt a b := by
    intro a ha
    refine hf a (by simp only [List.mem_append]; exact ha) b ?_
    rcases hb with hb | hb
    · exact List.mem_append.2 (Or.inl (mem_drop_of_succ hi hb))
    · exact List.mem_append.2 (Or.inr (mem_drop_of_succ hj hb))
  have new : PE.lt xs[i] b := by
    rcases hb with hb | hb
    · exact sorted_drop_lt hsx i hi b hb
    · rw [he]; exact sorted_drop_lt hsy j hj b hb
  rcases ha with (ha | rfl) | (ha | rfl)
  · exact old a (Or.inl ha)
  · exact new
  · exact old a (Or.inr ha)
  · rw [← he]; exact new

/-- The heads of what is left, when `xs[i] < ys[j]`: `xs[i]` is below all of `ys`'s rest. -/
theorem lt_rest {ys : List PE} (hw : AllWf ys) (hs : PE.Sorted ys) (j : Nat) (hj : j < ys.length)
    (x : PE) (hx : x.wf = true) (hlt : PE.lt x ys[j]) : ∀ b ∈ ys.drop j, PE.lt x b := by
  intro b hb
  rw [drop_cons' ys j hj] at hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hlt
  · exact lt_trans' hx (hw _ (List.getElem_mem hj)) (hw b (List.mem_of_mem_drop hb)) hlt
      (sorted_drop_lt hs j hj b hb)

/-- A consumed element is not left. -/
theorem front_not_left {xs ys : List PE} {i j : Nat} (hf : Front xs ys i j) (hwx : AllWf xs)
    (hwy : AllWf ys) (a : PE) (ha : a ∈ xs.take i ++ ys.take j)
    (hb : a ∈ xs.drop i ++ ys.drop j) : False := by
  have hwa : a.wf = true := by
    rcases List.mem_append.1 hb with h | h
    · exact hwx a (List.mem_of_mem_drop h)
    · exact hwy a (List.mem_of_mem_drop h)
  exact lt_irrefl a hwa (hf a ha a hb)


/-! ## Node lists: columns, appends -/

/-- A node list's keys. -/
abbrev keys (l : NL) : List PE := l.map (·.1)

theorem nlok_wf {l : NL} (hl : NLok l) : fpC.AllWf (keys l) := by
  intro k hk
  simp only [keys, List.mem_map] at hk
  obtain ⟨⟨k', S⟩, hm, rfl⟩ := hk
  exact (hl.2 k' S hm).1

theorem nl_unique : ∀ {l : NL}, NLok l → ∀ {k S S'}, (k, S) ∈ l → (k, S') ∈ l → S = S'
  | [], _, _, _, _, h, _ => by simp at h
  | (k0, S0) :: l, hl, k, S, S', h1, h2 => by
    have hs := hl.1
    simp only [List.map_cons, PE.Sorted, List.pairwise_cons] at hs
    have hl' : NLok l := ⟨hs.2, fun k S h => hl.2 k S (List.mem_cons_of_mem _ h)⟩
    have hw0 := (hl.2 k0 S0 (List.mem_cons_self ..)).1
    rcases List.mem_cons.1 h1 with h1 | h1 <;> rcases List.mem_cons.1 h2 with h2 | h2
    · cases h1; cases h2; rfl
    · cases h1
      exact absurd (hs.1 _ (List.mem_map_of_mem (f := (·.1)) h2)) (fpC.lt_irrefl _ hw0)
    · cases h2
      exact absurd (hs.1 _ (List.mem_map_of_mem (f := (·.1)) h1)) (fpC.lt_irrefl _ hw0)
    · exact nl_unique hl' h1 h2

/-- A node's column: the paths below its key are its set's. -/
theorem nl_col {l : NL} (hl : NLok l) {k : PE} {S : PathSet} (h : (k, S) ∈ l) (r : Path) :
    k :: r ∈ nlPaths l ↔ r ∈ S := by
  rw [mem_nlPaths]
  constructor
  · rintro ⟨k', S', r', h', hr', he⟩
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [nl_unique hl h h']; exact hr'
  · intro hr; exact ⟨k, S, r, h, hr, rfl⟩

theorem nl_nokey {l : NL} {k : PE} (h : k ∉ keys l) (r : Path) : k :: r ∉ nlPaths l := by
  rw [mem_nlPaths]
  rintro ⟨k', S', r', h', -, he⟩
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h (List.mem_map_of_mem (f := (·.1)) h')

theorem nl_heads {l : NL} (q : Path) (h : q ∈ nlPaths l) :
    ∃ k r, q = k :: r ∧ k ∈ keys l := by
  rw [mem_nlPaths] at h
  obtain ⟨k, S, r, hm, -, rfl⟩ := h
  exact ⟨k, r, rfl, List.mem_map_of_mem (f := (·.1)) hm⟩

theorem nlPaths_append (l l' : NL) (q : Path) :
    q ∈ nlPaths (l ++ l') ↔ q ∈ nlPaths l ∨ q ∈ nlPaths l' := by
  simp only [mem_nlPaths, List.mem_append]
  constructor
  · rintro ⟨k, S, r, (h | h), hr, rfl⟩
    · exact Or.inl ⟨k, S, r, h, hr, rfl⟩
    · exact Or.inr ⟨k, S, r, h, hr, rfl⟩
  · rintro (⟨k, S, r, h, hr, rfl⟩ | ⟨k, S, r, h, hr, rfl⟩)
    · exact ⟨k, S, r, Or.inl h, hr, rfl⟩
    · exact ⟨k, S, r, Or.inr h, hr, rfl⟩

theorem nlPaths_single (k : PE) (S : PathSet) (q : Path) :
    q ∈ nlPaths [(k, S)] ↔ ∃ r, r ∈ S ∧ q = k :: r := by
  simp only [mem_nlPaths, List.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨k', S', r, ⟨rfl, rfl⟩, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨k, S, r, ⟨rfl, rfl⟩, hr, rfl⟩

theorem nlok_snoc {lo : NL} (hl : NLok lo) {k : PE} {S : PathSet} (hlt : ∀ a ∈ keys lo, PE.lt a k)
    (hk : k.wf = true) (hne : ∃ r, r ∈ S) (hnil : [] ∉ S) : NLok (lo ++ [(k, S)]) := by
  refine ⟨?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, PE.Sorted]
    rw [List.pairwise_append]
    exact ⟨hl.1, List.pairwise_singleton _ _, fun a ha b hb => by
      simp at hb; subst hb; exact hlt a ha⟩
  · intro k' S' h
    rcases List.mem_append.1 h with h | h
    · exact hl.2 k' S' h
    · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hk, hne, hnil⟩

/-! ## The merge loops' invariant over node lists -/

/-- A key consumed by the merge of `l1` (up to `i`) and `l2` (up to `j`). -/
def proc (l1 l2 : NL) (i j : Nat) (k : PE) : Prop :=
  k ∈ (keys l1).take i ∨ k ∈ (keys l2).take j

/-- **The output of a merge so far**: a well-formed node list of the consumed keys, whose paths are
those of `R` below a consumed key. -/
def OInv (l1 l2 : NL) (i j : Nat) (lo : NL) (R : Path → Prop) : Prop :=
  NLok lo ∧ (∀ k ∈ keys lo, proc l1 l2 i j k) ∧
    ∀ q, q ∈ nlPaths lo ↔ R q ∧ ∃ k r, q = k :: r ∧ proc l1 l2 i j k

theorem oinv_zero (l1 l2 : NL) (R : Path → Prop) : OInv l1 l2 0 0 [] R := by
  refine ⟨⟨List.Pairwise.nil, fun _ _ h => by simp at h⟩, fun k h => by simp at h, fun q => ?_⟩
  simp only [mem_nlPaths_nil, false_iff, proc, List.take_zero, List.not_mem_nil, or_self]
  simp

/-- Consume a key `k`, appending the node `(k, S)`. -/
theorem oinv_add {l1 l2 : NL} {i j i' j' : Nat} {lo : NL} {R : Path → Prop} {k : PE} {S : PathSet}
    (h : OInv l1 l2 i j lo R) (hp : ∀ a, proc l1 l2 i' j' a ↔ proc l1 l2 i j a ∨ a = k)
    (hlt : ∀ a, proc l1 l2 i j a → PE.lt a k) (hk : k.wf = true) (hne : ∃ r, r ∈ S)
    (hnil : [] ∉ S) (hcol : ∀ r, R (k :: r) ↔ r ∈ S) : OInv l1 l2 i' j' (lo ++ [(k, S)]) R := by
  obtain ⟨hok, hkeys, hmem⟩ := h
  refine ⟨nlok_snoc hok (fun a ha => hlt a (hkeys a ha)) hk hne hnil, ?_, fun q => ?_⟩
  · intro a ha
    simp only [keys, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_singleton] at ha
    rw [hp]
    rcases ha with ha | rfl
    · exact Or.inl (hkeys a ha)
    · exact Or.inr rfl
  · rw [nlPaths_append, hmem, nlPaths_single]
    constructor
    · rintro (⟨hR, k', r, rfl, hpr⟩ | ⟨r, hr, rfl⟩)
      · exact ⟨hR, k', r, rfl, (hp k').2 (Or.inl hpr)⟩
      · exact ⟨(hcol r).2 hr, k, r, rfl, (hp k).2 (Or.inr rfl)⟩
    · rintro ⟨hR, k', r, rfl, hpr⟩
      rcases (hp k').1 hpr with hpr | rfl
      · exact Or.inl ⟨hR, k', r, rfl, hpr⟩
      · exact Or.inr ⟨r, (hcol r).1 hR, rfl⟩

/-- Consume a key `k` with nothing of `R` below it. -/
theorem oinv_skip {l1 l2 : NL} {i j i' j' : Nat} {lo : NL} {R : Path → Prop} {k : PE}
    (h : OInv l1 l2 i j lo R) (hp : ∀ a, proc l1 l2 i' j' a ↔ proc l1 l2 i j a ∨ a = k)
    (hcol : ∀ r, ¬ R (k :: r)) : OInv l1 l2 i' j' lo R := by
  obtain ⟨hok, hkeys, hmem⟩ := h
  refine ⟨hok, fun a ha => (hp a).2 (Or.inl (hkeys a ha)), fun q => ?_⟩
  rw [hmem]
  constructor
  · rintro ⟨hR, k', r, rfl, hpr⟩; exact ⟨hR, k', r, rfl, (hp k').2 (Or.inl hpr)⟩
  · rintro ⟨hR, k', r, rfl, hpr⟩
    rcases (hp k').1 hpr with hpr | rfl
    · exact ⟨hR, k', r, rfl, hpr⟩
    · exact absurd hR (hcol r)

/-- At the end (both lists consumed), the output's paths are `R`'s. -/
theorem oinv_final {l1 l2 : NL} {lo : NL} {R : Path → Prop}
    (h : OInv l1 l2 l1.length l2.length lo R)
    (hR : ∀ q, R q → ∃ k r, q = k :: r ∧ (k ∈ keys l1 ∨ k ∈ keys l2)) :
    ∀ q, q ∈ nlPaths lo ↔ R q := by
  intro q
  rw [h.2.2]
  constructor
  · exact fun h => h.1
  · intro hq
    obtain ⟨k, r, rfl, hk⟩ := hR q hq
    refine ⟨hq, k, r, rfl, ?_⟩
    unfold proc
    have e1 : (keys l1).take l1.length = keys l1 := List.take_of_length_le (by simp [keys])
    have e2 : (keys l2).take l2.length = keys l2 := List.take_of_length_le (by simp [keys])
    rw [e1, e2]; exact hk

theorem proc_succ1 {l1 l2 : NL} {i j : Nat} (hi : i < l1.length) (a : PE) :
    proc l1 l2 (i + 1) j a ↔ proc l1 l2 i j a ∨ a = l1[i].1 := by
  unfold proc
  rw [fpC.take_succ' (keys l1) i (by simp [hi])]
  simp only [List.mem_append, List.mem_singleton, keys, List.getElem_map]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)

theorem proc_succ2 {l1 l2 : NL} {i j : Nat} (hj : j < l2.length) (a : PE) :
    proc l1 l2 i (j + 1) a ↔ proc l1 l2 i j a ∨ a = l2[j].1 := by
  unfold proc
  rw [fpC.take_succ' (keys l2) j (by simp [hj])]
  simp only [List.mem_append, List.mem_singleton, keys, List.getElem_map]
  constructor
  · rintro (h | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem proc_succ12 {l1 l2 : NL} {i j : Nat} (hi : i < l1.length) (hj : j < l2.length)
    (he : l1[i].1 = l2[j].1) (a : PE) :
    proc l1 l2 (i + 1) (j + 1) a ↔ proc l1 l2 i j a ∨ a = l1[i].1 := by
  rw [proc_succ2 hj, proc_succ1 hi, he, or_assoc, or_self]

/-- Consumed keys are below the next key of either list. -/
theorem proc_lt1 {l1 l2 : NL} {i j : Nat} (hf : fpC.Front (keys l1) (keys l2) i j)
    (hi : i < l1.length) (a : PE) (ha : proc l1 l2 i j a) : PE.lt a l1[i].1 := by
  refine hf a (List.mem_append.2 ha) _ (List.mem_append.2 (Or.inl ?_))
  rw [fpC.drop_cons' (keys l1) i (by simp [hi])]
  simp [keys]

theorem proc_lt2 {l1 l2 : NL} {i j : Nat} (hf : fpC.Front (keys l1) (keys l2) i j)
    (hj : j < l2.length) (a : PE) (ha : proc l1 l2 i j a) : PE.lt a l2[j].1 := by
  refine hf a (List.mem_append.2 ha) _ (List.mem_append.2 (Or.inr ?_))
  rw [fpC.drop_cons' (keys l2) j (by simp [hj])]
  simp [keys]

/-- The next key of `l1`, below the rest of `l2`, is not a key of `l2`. -/
theorem fresh1 {l1 l2 : NL} {i j : Nat} (h1 : NLok l1)
    (hf : fpC.Front (keys l1) (keys l2) i j) (hi : i < l1.length)
    (hlt : ∀ b ∈ (keys l2).drop j, PE.lt l1[i].1 b) : l1[i].1 ∉ keys l2 := by
  intro hm
  have hw : l1[i].1.wf = true := nlok_wf h1 _ (List.mem_map_of_mem (f := (·.1)) (List.getElem_mem hi))
  rw [← List.take_append_drop j (keys l2)] at hm
  rcases List.mem_append.1 hm with hm | hm
  · exact fpC.lt_irrefl _ hw (proc_lt1 hf hi _ (Or.inr hm))
  · exact fpC.lt_irrefl _ hw (hlt _ hm)

theorem fresh2 {l1 l2 : NL} {i j : Nat} (h2 : NLok l2)
    (hf : fpC.Front (keys l1) (keys l2) i j) (hj : j < l2.length)
    (hlt : ∀ b ∈ (keys l1).drop i, PE.lt l2[j].1 b) : l2[j].1 ∉ keys l1 := by
  intro hm
  have hw : l2[j].1.wf = true := nlok_wf h2 _ (List.mem_map_of_mem (f := (·.1)) (List.getElem_mem hj))
  rw [← List.take_append_drop i (keys l1)] at hm
  rcases List.mem_append.1 hm with hm | hm
  · exact fpC.lt_irrefl _ hw (proc_lt2 hf hj _ (Or.inl hm))
  · exact fpC.lt_irrefl _ hw (hlt _ hm)

/-- A key left in `l1` once `l2` is consumed is not a key of `l2`. -/
theorem notin_other1 {l1 l2 : NL} {i : Nat} (h1 : NLok l1)
    (hf : Front (keys l1) (keys l2) i l2.length) {k : PE} {S : PathSet} (hm : (k, S) ∈ l1.drop i) :
    k ∉ keys l2 := by
  intro hk
  have hw : k.wf = true := (h1.2 k S (List.mem_of_mem_drop hm)).1
  have hk' : k ∈ (keys l2).take l2.length := by rw [List.take_of_length_le (by simp [keys])]; exact hk
  have hd : k ∈ (keys l1).drop i := by
    simp only [keys, ← List.map_drop]; exact List.mem_map_of_mem (f := (·.1)) hm
  exact lt_irrefl k hw (hf k (List.mem_append.2 (Or.inr hk')) k (List.mem_append.2 (Or.inl hd)))

theorem notin_other2 {l1 l2 : NL} {j : Nat} (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) l1.length j) {k : PE} {S : PathSet} (hm : (k, S) ∈ l2.drop j) :
    k ∉ keys l1 := by
  intro hk
  have hw : k.wf = true := (h2.2 k S (List.mem_of_mem_drop hm)).1
  have hk' : k ∈ (keys l1).take l1.length := by rw [List.take_of_length_le (by simp [keys])]; exact hk
  have hd : k ∈ (keys l2).drop j := by
    simp only [keys, ← List.map_drop]; exact List.mem_map_of_mem (f := (·.1)) hm
  exact lt_irrefl k hw (hf k (List.mem_append.2 (Or.inl hk')) k (List.mem_append.2 (Or.inr hd)))

theorem nlok_sorted {l : NL} (h : NLok l) : PE.Sorted (keys l) := h.1

theorem getElem_mem_drop {l : NL} {i : Nat} (hi : i < l.length) : l[i] ∈ l.drop i := by
  rw [drop_cons' l i hi]; exact List.mem_cons_self ..

/-- **`l1`'s rest appended** once `l2` is consumed. -/
theorem oinv_tail1 {l1 l2 : NL} {R : Path → Prop} (h1 : NLok l1) :
    ∀ (n i : Nat) (lo : NL), n = l1.length - i → i ≤ l1.length →
    OInv l1 l2 i l2.length lo R → Front (keys l1) (keys l2) i l2.length →
    (∀ k S r, (k, S) ∈ l1.drop i → (R (k :: r) ↔ r ∈ S)) →
    OInv l1 l2 l1.length l2.length (lo ++ l1.drop i) R
  | 0, i, lo, hn, hi, ho, _, _ => by
    have : i = l1.length := by omega
    subst this; simp only [List.drop_length, List.append_nil]; exact ho
  | n + 1, i, lo, hn, hi, ho, hf, hcol => by
    have hi' : i < l1.length := by omega
    have hk : (keys l1)[i]'(by simp [hi']) = l1[i].1 := by simp [keys]
    have hm := getElem_mem_drop hi'
    obtain ⟨hw, hne, hnil⟩ := h1.2 l1[i].1 l1[i].2 (List.mem_of_mem_drop hm)
    have ho' := oinv_add (k := l1[i].1) (S := l1[i].2) ho (proc_succ1 hi')
      (proc_lt1 hf hi') hw hne hnil (fun r => hcol _ _ r hm)
    have hf' : Front (keys l1) (keys l2) (i + 1) l2.length :=
      front_step_x (nlok_sorted h1) hf (by simp [hi']) (fun b hb => by
        rw [List.drop_of_length_le (by simp [keys])] at hb; simp at hb)
    have := oinv_tail1 h1 n (i + 1) (lo ++ [(l1[i].1, l1[i].2)]) (by omega) hi' ho' hf'
      (fun k S r h => hcol k S r (mem_drop_of_succ hi' h))
    rw [List.append_assoc, List.singleton_append, ← drop_cons' l1 i hi'] at this
    exact this

/-- `l2`'s rest appended once `l1` is consumed. -/
theorem oinv_tail2 {l1 l2 : NL} {R : Path → Prop} (h2 : NLok l2) :
    ∀ (n j : Nat) (lo : NL), n = l2.length - j → j ≤ l2.length →
    OInv l1 l2 l1.length j lo R → Front (keys l1) (keys l2) l1.length j →
    (∀ k S r, (k, S) ∈ l2.drop j → (R (k :: r) ↔ r ∈ S)) →
    OInv l1 l2 l1.length l2.length (lo ++ l2.drop j) R
  | 0, j, lo, hn, hj, ho, _, _ => by
    have : j = l2.length := by omega
    subst this; simp only [List.drop_length, List.append_nil]; exact ho
  | n + 1, j, lo, hn, hj, ho, hf, hcol => by
    have hj' : j < l2.length := by omega
    have hm := getElem_mem_drop hj'
    obtain ⟨hw, hne, hnil⟩ := h2.2 l2[j].1 l2[j].2 (List.mem_of_mem_drop hm)
    have ho' := oinv_add (k := l2[j].1) (S := l2[j].2) ho (proc_succ2 hj')
      (proc_lt2 hf hj') hw hne hnil (fun r => hcol _ _ r hm)
    have hf' : Front (keys l1) (keys l2) l1.length (j + 1) :=
      front_step_y (nlok_sorted h2) hf (by simp [hj']) (fun b hb => by
        rw [List.drop_of_length_le (by simp [keys])] at hb; simp at hb)
    have := oinv_tail2 h2 n (j + 1) (lo ++ [(l2[j].1, l2[j].2)]) (by omega) hj' ho' hf'
      (fun k S r h => hcol k S r (mem_drop_of_succ hj' h))
    rw [List.append_assoc, List.singleton_append, ← drop_cons' l2 j hj'] at this
    exact this

/-! ## `SetNodeMap.Union`'s steps -/

/-- The union of two node lists' paths. -/
abbrev RU (l1 l2 : NL) : Path → Prop := fun q => q ∈ nlPaths l1 ∨ q ∈ nlPaths l2

theorem lt_rest_nl {l : NL} (h : NLok l) {j : Nat} (hj : j < l.length) {x : PE} (hx : x.wf = true)
    (hlt : PE.lt x l[j].1) : ∀ b ∈ (keys l).drop j, PE.lt x b :=
  lt_rest (nlok_wf h) (nlok_sorted h) j (by simp [hj]) x hx (by simpa [keys] using hlt)

theorem nl_mem_get {l : NL} {i : Nat} (hi : i < l.length) : l[i] ∈ l := List.getElem_mem hi

theorem nl_col' {l : NL} (hl : NLok l) {p : PE × PathSet} (h : p ∈ l) (r : Path) :
    p.1 :: r ∈ nlPaths l ↔ r ∈ p.2 := nl_col hl (k := p.1) (S := p.2) h r

theorem union_step1 {l1 l2 : NL} {i j : Nat} {lo : NL} (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RU l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (hlt : PE.lt l1[i].1 l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) j ∧ OInv l1 l2 (i + 1) j (lo ++ [l1[i]]) (RU l1 l2) := by
  obtain ⟨hw, hne, hnil⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  have hr := lt_rest_nl h2 hj hw hlt
  refine ⟨front_step_x (nlok_sorted h1) hf (by simp [hi]) (by simpa [keys] using hr), ?_⟩
  have := oinv_add (k := l1[i].1) (S := l1[i].2) ho (proc_succ1 hi) (proc_lt1 hf hi) hw hne hnil
    (fun r => by
      simp only [RU]
      rw [nl_col' h1 (nl_mem_get hi) r]
      have := nl_nokey (fresh1 h1 hf hi hr) r
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h this
      · exact Or.inl)
  simpa using this

theorem union_step2 {l1 l2 : NL} {i j : Nat} {lo : NL} (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RU l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (hlt : PE.lt l2[j].1 l1[i].1) :
    Front (keys l1) (keys l2) i (j + 1) ∧ OInv l1 l2 i (j + 1) (lo ++ [l2[j]]) (RU l1 l2) := by
  obtain ⟨hw, hne, hnil⟩ := h2.2 l2[j].1 l2[j].2 (nl_mem_get hj)
  have hr := lt_rest_nl h1 hi hw hlt
  refine ⟨front_step_y (nlok_sorted h2) hf (by simp [hj]) (by simpa [keys] using hr), ?_⟩
  have := oinv_add (k := l2[j].1) (S := l2[j].2) ho (proc_succ2 hj) (proc_lt2 hf hj) hw hne hnil
    (fun r => by
      simp only [RU]
      rw [nl_col' h2 (nl_mem_get hj) r]
      have := nl_nokey (fresh2 h2 hf hj hr) r
      constructor
      · rintro (h | h)
        · exact absurd h this
        · exact h
      · exact Or.inr)
  simpa using this

theorem union_step12 {l1 l2 : NL} {i j : Nat} {lo : NL} (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RU l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (he : l1[i].1 = l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) (j + 1) ∧
      OInv l1 l2 (i + 1) (j + 1) (lo ++ [(l1[i].1, PathSet.union l1[i].2 l2[j].2)]) (RU l1 l2) := by
  obtain ⟨hw, hne, hnil⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  obtain ⟨-, -, hnil2⟩ := h2.2 l2[j].1 l2[j].2 (nl_mem_get hj)
  refine ⟨front_step_eq (nlok_sorted h1) (nlok_sorted h2) hf (by simp [hi]) (by simp [hj])
    (by simpa [keys] using he), ?_⟩
  obtain ⟨q, hq⟩ := hne
  refine oinv_add ho (proc_succ12 hi hj he) (proc_lt1 hf hi) hw ⟨q, (mem_punion _ _ q).2 (Or.inl hq)⟩
    (fun h => by
      rcases (mem_punion _ _ _).1 h with h | h
      · exact hnil h
      · exact hnil2 h) (fun r => ?_)
  simp only [RU]
  rw [mem_punion, nl_col' h1 (nl_mem_get hi) r]
  have : l1[i].1 = l2[j].1 := he
  rw [this, nl_col' h2 (nl_mem_get hj) r]

theorem union_final {l1 l2 : NL} {lo : NL} (ho : OInv l1 l2 l1.length l2.length lo (RU l1 l2))
    (D1 D2 : PathSet) (hD1 : ∀ q, q ∈ D1 ↔ q ∈ nlPaths l1) (hD2 : ∀ q, q ∈ D2 ↔ q ∈ nlPaths l2) :
    ∀ q, q ∈ PathSet.union D1 D2 ↔ q ∈ nlPaths lo := by
  intro q
  rw [oinv_final ho (fun q hq => by
    rcases hq with h | h
    · obtain ⟨k, r, rfl, hk⟩ := nl_heads q h; exact ⟨k, r, rfl, Or.inl hk⟩
    · obtain ⟨k, r, rfl, hk⟩ := nl_heads q h; exact ⟨k, r, rfl, Or.inr hk⟩), mem_punion, hD1, hD2]

theorem union_tail1 {l1 l2 : NL} {i : Nat} {lo : NL} (h1 : NLok l1) (hi : i ≤ l1.length)
    (hf : Front (keys l1) (keys l2) i l2.length) (ho : OInv l1 l2 i l2.length lo (RU l1 l2)) :
    OInv l1 l2 l1.length l2.length (lo ++ l1.drop i) (RU l1 l2) :=
  oinv_tail1 h1 _ i lo rfl hi ho hf (fun k S r hm => by
    simp only [RU]
    rw [nl_col h1 (List.mem_of_mem_drop hm) r]
    have := nl_nokey (notin_other1 h1 hf hm) r
    exact ⟨fun h => h.elim id (fun h' => absurd h' this), Or.inl⟩)

theorem union_tail2 {l1 l2 : NL} {j : Nat} {lo : NL} (h2 : NLok l2) (hj : j ≤ l2.length)
    (hf : Front (keys l1) (keys l2) l1.length j) (ho : OInv l1 l2 l1.length j lo (RU l1 l2)) :
    OInv l1 l2 l1.length l2.length (lo ++ l2.drop j) (RU l1 l2) :=
  oinv_tail2 h2 _ j lo rfl hj ho hf (fun k S r hm => by
    simp only [RU]
    rw [nl_col h2 (List.mem_of_mem_drop hm) r]
    have := nl_nokey (notin_other2 h2 hf hm) r
    exact ⟨fun h => h.elim (fun h' => absurd h' this) id, Or.inr⟩)

end fpC

/-! ## The representation, viewed as members and node lists -/

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace fpC

theorem trieRep_mk_eq (p : Loc) (ms : List PE) (cs : List (PE × Trie)) :
    trieRep (GF := GF) p (.mk ms cs) = iprop(∃ (v : fieldpath.Set') (es : List fieldpath.PathElement)
      (ns : List fieldpath.setNode),
      p ↦□ v ∗ v.Members'.members' ↦*{DFrac.discard} es ∗ isPEL es ms ∗
      v.Children'.members' ↦*{DFrac.discard} ns ∗ trieRepC ns cs) := by
  simp only [trieRep]

theorem trieRepC_nil_eq : trieRepC (GF := GF) [] [] = iprop(True) := by simp only [trieRepC]

theorem trieRepC_cons_eq (n : fieldpath.setNode) (ns : List fieldpath.setNode) (pe : PE) (t : Trie)
    (cs : List (PE × Trie)) :
    trieRepC (GF := GF) (n :: ns) ((pe, t) :: cs) =
      iprop(isPE n.pathElement' pe ∗ trieRep n.set' t ∗ trieRepC ns cs) := by
  simp only [trieRepC]

/-- A `SetNodeMap`'s nodes as (path element, set) pairs: each node's element and `isSet`. -/
def nodesL : List fieldpath.setNode → NL → IProp GF
  | [], [] => iprop(True)
  | n :: ns, (k, S) :: l => iprop(isPE n.pathElement' k ∗ isSet n.set' S ∗ nodesL ns l)
  | _, _ => iprop(False)

instance nodesL_pers : (ns : List fieldpath.setNode) → (l : NL) → Persistent (nodesL (GF := GF) ns l)
  | [], [] => by unfold nodesL; infer_instance
  | [], _ :: _ => by unfold nodesL; infer_instance
  | _ :: _, [] => by unfold nodesL; infer_instance
  | n :: ns, (k, S) :: l => by
      unfold nodesL
      have := nodesL_pers ns l
      infer_instance

theorem nodesL_cons_eq (n : fieldpath.setNode) (ns : List fieldpath.setNode) (k : PE) (S : PathSet)
    (l : NL) : nodesL (GF := GF) (n :: ns) ((k, S) :: l) =
      iprop(isPE n.pathElement' k ∗ isSet n.set' S ∗ nodesL ns l) := by
  simp only [nodesL]

theorem nodesL_nil_eq : nodesL (GF := GF) [] [] = iprop(True) := by simp only [nodesL]

theorem nodesL_length : ∀ (ns : List fieldpath.setNode) (l : NL),
    nodesL (GF := GF) ns l ⊢ ⌜ns.length = l.length⌝
  | [], [] => by iintro _; ipureintro; rfl
  | [], _ :: _ => by unfold nodesL; iintro %h; exact h.elim
  | _ :: _, [] => by unfold nodesL; iintro %h; exact h.elim
  | n :: ns, (k, S) :: l => by
    rw [nodesL_cons_eq]; iintro ⟨-, -, H⟩
    ihave %h := nodesL_length ns l $$ H
    ipureintro; simp [h]

theorem nodesL_wf : ∀ (ns : List fieldpath.setNode) (l : NL),
    nodesL (GF := GF) ns l ⊢ ⌜∀ k S, (k, S) ∈ l → k.wf = true⌝
  | [], [] => by iintro _; ipureintro; simp
  | [], _ :: _ => by unfold nodesL; iintro %h; exact h.elim
  | _ :: _, [] => by unfold nodesL; iintro %h; exact h.elim
  | n :: ns, (k, S) :: l => by
    rw [nodesL_cons_eq]; iintro ⟨He, -, H⟩
    ihave %h1 := fpL.isPE_wf' _ _ $$ He
    ihave %h2 := nodesL_wf ns l $$ H
    ipureintro
    intro k' S' hk
    rcases List.mem_cons.1 hk with h | h
    · cases h; exact h1
    · exact h2 k' S' h

theorem nodesL_app : ∀ (ns ns' : List fieldpath.setNode) (l l' : NL), ns.length = l.length →
    (nodesL (GF := GF) (ns ++ ns') (l ++ l') ⊣⊢ nodesL ns l ∗ nodesL ns' l')
  | [], ns', [], l', _ => by
    simp only [List.nil_append, nodesL_nil_eq]
    exact ⟨by iintro H; iframe H, by iintro ⟨-, H⟩; iexact H⟩
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | n :: ns, ns', (k, S) :: l, l', h => by
    simp only [List.cons_append]
    have ih := nodesL_app ns ns' l l' (by simpa using h)
    simp only [nodesL_cons_eq]
    constructor
    · iintro ⟨He, Hs, H⟩
      icases ih.1 $$ H with ⟨H1, H2⟩
      iframe
    · iintro ⟨⟨He, Hs, H1⟩, H2⟩
      iframe
      iapply ih.2; iframe

theorem nodesL_lookup : ∀ (ns : List fieldpath.setNode) (l : NL) (k : Nat) (n : fieldpath.setNode),
    ns[k]? = some n → nodesL (GF := GF) ns l ⊢
      ∃ pe S, ⌜l[k]? = some (pe, S)⌝ ∗ isPE n.pathElement' pe ∗ isSet n.set' S
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold nodesL; iintro %h; exact h.elim
  | n' :: ns, (k', S') :: l, 0, n, h => by
    simp at h; subst h
    rw [nodesL_cons_eq]; iintro ⟨He, Hs, -⟩; iexists k', S'; iframe; ipureintro; rfl
  | n' :: ns, (k', S') :: l, k + 1, n, h => by
    simp at h
    rw [nodesL_cons_eq]; iintro ⟨-, -, H⟩
    simp only [List.getElem?_cons_succ]
    iapply nodesL_lookup ns l k n h; iexact H

theorem trieRepC_nodesL : ∀ (ns : List fieldpath.setNode) (cs : List (PE × Trie)),
    Trie.CanonicalC cs → trieRepC (GF := GF) ns cs ⊢ nodesL ns (nlOf cs)
  | [], [], _ => by
    rw [trieRepC_nil_eq, show nlOf [] = [] from rfl, nodesL_nil_eq]
  | [], _ :: _, _ => by unfold trieRepC; iintro %h; exact h.elim
  | _ :: _, [], _ => by unfold trieRepC; iintro %h; exact h.elim
  | n :: ns, (pe, t) :: cs, hc => by
    simp only [Trie.CanonicalC] at hc
    rw [trieRepC_cons_eq, show nlOf ((pe, t) :: cs) = (pe, tset t) :: nlOf cs from rfl,
      nodesL_cons_eq]
    iintro ⟨He, Ht, H⟩
    iframe He
    isplitl [Ht]
    · unfold isSet; iexists t; iframe; ipureintro
      exact ⟨hc.1, fun q => (mem_tset t q).symm⟩
    · iapply trieRepC_nodesL ns cs hc.2.2; iexact H

theorem nodesL_trieRepC : ∀ (ns : List fieldpath.setNode) (l : NL),
    (∀ k S, (k, S) ∈ l → ∃ q, q ∈ S) →
    nodesL (GF := GF) ns l ⊢ ∃ cs, trieRepC ns cs ∗ ⌜Trie.CanonicalC cs ∧ nlOf cs = l⌝
  | [], [], _ => by
    iintro _; iexists []; rw [trieRepC_nil_eq]; isplit
    · itrivial
    · ipureintro; exact ⟨trivial, rfl⟩
  | [], _ :: _, _ => by unfold nodesL; iintro %h; exact h.elim
  | _ :: _, [], _ => by unfold nodesL; iintro %h; exact h.elim
  | n :: ns, (k, S) :: l, hne => by
    rw [nodesL_cons_eq]
    iintro ⟨He, Hs, H⟩
    icases nodesL_trieRepC ns l (fun k' S' h => hne k' S' (List.mem_cons_of_mem _ h)) $$ H
      with ⟨%cs, Hc, %hc⟩
    unfold isSet
    icases Hs with ⟨%t, %ht, Ht⟩
    iexists (k, t) :: cs
    rw [trieRepC_cons_eq]
    iframe
    ipureintro
    obtain ⟨q, hq⟩ := hne k S (List.mem_cons_self ..)
    refine ⟨⟨ht.1, ⟨q, (ht.2 q).2 hq⟩, hc.1⟩, ?_⟩
    simp only [nlOf, List.map_cons]
    have e : tset t = S := FSet.ext' (fun q => by rw [mem_tset]; exact ht.2 q)
    rw [e]
    simp only [nlOf] at hc
    rw [hc.2]

theorem nodesL_append (ns ns' : List fieldpath.setNode) (l l' : NL) :
    nodesL (GF := GF) ns l ∗ nodesL ns' l' ⊢ nodesL (ns ++ ns') (l ++ l') := by
  iintro ⟨H1, H2⟩
  ihave %h := nodesL_length ns l $$ H1
  iapply (nodesL_app ns ns' l l' h).2
  iframe

theorem nodesL_snoc (ns : List fieldpath.setNode) (l : NL) (n : fieldpath.setNode) (k : PE)
    (S : PathSet) :
    nodesL (GF := GF) ns l ∗ isPE n.pathElement' k ∗ isSet n.set' S ⊢
      nodesL (ns ++ [n]) (l ++ [(k, S)]) := by
  iintro ⟨H1, He, Hs⟩
  iapply nodesL_append
  iframe
  rw [nodesL_cons_eq, nodesL_nil_eq]
  iframe

theorem nodesL_drop (ns : List fieldpath.setNode) (l : NL) (k : Nat) :
    nodesL (GF := GF) ns l ⊢ nodesL (ns.drop k) (l.drop k) := by
  iintro H
  ihave %hl := nodesL_length ns l $$ H
  have e := (nodesL_app (GF := GF) (ns.take k) (ns.drop k) (l.take k) (l.drop k)
    (by simp [hl])).1
  rw [List.take_append_drop, List.take_append_drop] at e
  icases e $$ H with ⟨-, H⟩
  iexact H

/-- **A node of a `SetNodeMap`'s slice**: its fields' persistent points-tos, its element and set. -/
theorem node_at (sl : GoSlice) (ns : List fieldpath.setNode) (nl : NL) (k : Int) (n : fieldpath.setNode)
    (hk : 0 ≤ k) (hn : ns[k.toNat]? = some n) :
    sl ↦*{DFrac.discard} ns ∗ nodesL (GF := GF) ns nl ⊢
      ∃ pe S, ⌜nl[k.toNat]? = some (pe, S)⌝ ∗
        (sliceIndexRef fieldpath.setNode k sl).[fieldpath.setNode, go!"pathElement"] ↦□ n.pathElement' ∗
        (sliceIndexRef fieldpath.setNode k sl).[fieldpath.setNode, go!"set"] ↦□ n.set' ∗
        isPE n.pathElement' pe ∗ isSet n.set' S := by
  iintro ⟨#Hs, #Hl⟩
  icases ownSlice_elem_acc k n sl DFrac.discard ns hk hn $$ Hs with ⟨#He, -⟩
  icases nodesL_lookup ns nl k.toNat n hn $$ Hl with ⟨%pe, %S, %h, #Hpe, #HS⟩
  iStructNamed He
  iexists pe, S
  iframe #
  ipureintro; exact h

/-- **The node-list view of a `SetNodeMap`.** -/
theorem isNodesV_view (m : fieldpath.SetNodeMap) (D : PathSet) :
    isNodesV (GF := GF) m D ⊣⊢ ∃ ns l, m.members' ↦*{DFrac.discard} ns ∗ nodesL ns l ∗
      ⌜NLok l ∧ ∀ q, q ∈ D ↔ q ∈ nlPaths l⌝ := by
  constructor
  · unfold isNodesV
    iintro ⟨%ns, %cs, Hm, Hc, %h⟩
    ihave #Hl := trieRepC_nodesL ns cs h.2.1 $$ Hc
    ihave %hw := nodesL_wf ns (nlOf cs) $$ Hl
    iexists ns, nlOf cs
    iframe
    isplit
    · iexact Hl
    ipureintro
    refine ⟨⟨?_, ?_⟩, fun q => by rw [← h.2.2 q, pathsC_nlOf]⟩
    · rw [nlOf_keys]; exact h.1
    · intro k S hk
      refine ⟨hw k S hk, ?_⟩
      simp only [nlOf, List.mem_map] at hk
      obtain ⟨⟨e, t⟩, hm, he⟩ := hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨-, q, hq⟩ := canonicalC_mem cs e t h.2.1 hm
      exact ⟨tset_nonempty_of _ _ hq, fun hn => paths_ne_nil t ((mem_tset t []).1 hn)⟩
  · unfold isNodesV
    iintro ⟨%ns, %l, Hm, #Hl, %h⟩
    icases nodesL_trieRepC ns l (fun k S hk => (h.1.2 k S hk).2.1) $$ Hl with ⟨%cs, Hc, %hc⟩
    iexists ns, cs
    iframe
    isplit
    · iexact Hc
    ipureintro
    refine ⟨?_, hc.1, fun q => ?_⟩
    · rw [← nlOf_keys, hc.2]; exact h.1.1
    · rw [pathsC_nlOf, hc.2, h.2 q]

/-- **The members/children view of a set.** -/
theorem isSet_view (p : Loc) (S : PathSet) :
    isSet (GF := GF) p S ⊣⊢ ∃ v : fieldpath.Set', p ↦□ v ∗
      isPESetV v.Members' DFrac.discard S.tops ∗ isNodesV v.Children' S.deep ∗ ⌜[] ∉ S⌝ := by
  constructor
  · unfold isSet
    iintro ⟨%t, %ht, Ht⟩
    obtain ⟨ms, cs⟩ := t
    rw [trieRep_mk_eq]
    icases Ht with ⟨%v, %es, %ns, Hp, Hes, Hms, Hns, Hcs⟩
    simp only [Trie.Canonical] at ht
    iexists v
    iframe Hp
    isplitl [Hes Hms]
    · unfold isPESetV
      iexists es, ms
      iframe
      ipureintro
      refine ⟨ht.1.1, FSet.ext' (fun e => ?_)⟩
      rw [FSet.mem_ofList', PathSet_mem_tops_law_holds, ← ht.2, paths_mk]
      constructor
      · intro h; exact Or.inl ⟨e, rfl, h⟩
      · rintro (⟨e', he, h⟩ | h)
        · cases he; exact h
        · exact absurd h (pathsC_single cs e)
    isplitl [Hns Hcs]
    · unfold isNodesV
      iexists ns, cs
      iframe
      ipureintro
      refine ⟨ht.1.2.1, ht.1.2.2, fun q => ?_⟩
      rw [PathSet_mem_deep_law_holds, ← ht.2, paths_mk]
      constructor
      · intro h; exact ⟨Or.inr h, pathsC_len cs q h⟩
      · rintro ⟨⟨e, rfl, -⟩ | h, hl⟩
        · simp at hl
        · exact h
    · ipureintro
      intro h
      have := (ht.2 []).2 h
      rw [paths_mk] at this
      rcases this with ⟨e, he, -⟩ | h
      · cases he
      · exact pathsC_ne_nil cs h
  · iintro ⟨%v, #Hp, Hm, Hc, %hne⟩
    unfold isPESetV isNodesV
    icases Hm with ⟨%es, %xs, Hes, Hxs, %hx⟩
    icases Hc with ⟨%ns, %cs, Hns, Hcs, %hc⟩
    unfold isSet
    iexists .mk xs cs
    isplit
    · ipureintro
      refine ⟨⟨hx.1, hc.1, hc.2.1⟩, fun q => ?_⟩
      rw [paths_mk]
      match q with
      | [] =>
        constructor
        · rintro (⟨e, he, -⟩ | h)
          · cases he
          · exact absurd h (pathsC_ne_nil cs)
        · intro h; exact absurd h hne
      | [e] =>
        rw [← PathSet_mem_tops_law_holds, ← hx.2, FSet.mem_ofList']
        constructor
        · rintro (⟨e', he, h⟩ | h)
          · cases he; exact h
          · exact absurd h (pathsC_single cs e)
        · intro h; exact Or.inl ⟨e, rfl, h⟩
      | e :: e' :: r =>
        rw [hc.2.2, PathSet_mem_deep_law_holds]
        simp
    · rw [trieRep_mk_eq]
      iexists v, es, ns
      iframe
      iframe #

end fpC
end views

end smd
end EtcdGrove
end Perennial
