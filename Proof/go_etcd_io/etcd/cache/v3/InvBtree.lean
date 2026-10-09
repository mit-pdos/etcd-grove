/-
The btree `k8s.io/utils/third_party/forked/golang/btree` (a fork of `google/btree`), as
etcd's `cache` store sees it: the store's model-level predicate `ownBTree` and triples
(`*.modelSpec`), defined over and derived from the btree's own proof
(`Proof/k8s_io/.../btree/`, `*.modelSpec_of`). Lean-first (no Rocq counterpart).

The model of a tree is the list of its items in order, `items : List V`, for a relation
`isItem : T' → V → IProp GF` (persistent) between a Go item and its model and a relation
`less : V → V → Prop` that the tree's Go `LessFunc` decides (`btLessSpec`). Go's btree
documentation asks `less` to be "a strict ordering" and calls two items equal when
neither is less than the other: `StrictWeakOrder` is the hypothesis every spec takes, and
`btFind`/`btInsert`/`btDelete` are lookup, replace-or-insert and delete on a list sorted by
`less` (they scan past the smaller items and then compare with one item).

The pure part: those operations, the visited sublists of the iterations, and the lemmas
the store's proofs use (sortedness, membership).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Spec.k8s_io.utils.third_party.forked.golang.btree.New
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__ReplaceOrInsert
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Get
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Delete
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Clone
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__AscendGreaterOrEqual
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__AscendRange
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Fractional

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-! ## Pure definitions -/

/-- Go's `LessFunc` contract ("It should implement a strict ordering"), as the btree's
code needs it: irreflexive, transitive, and incomparability ("equal" items) transitive. -/
structure StrictWeakOrder {V : Type} (less : V → V → Prop) : Prop where
  irrefl : ∀ a, ¬ less a a
  trans : ∀ a b c, less a b → less b c → less a c
  incomp_trans : ∀ a b c, ¬ less a b → ¬ less b a → ¬ less b c → ¬ less c b →
    ¬ less a c ∧ ¬ less c a

section ops
variable {V : Type} (less : V → V → Prop) [DecidableRel less]

/-- `Get(key)` on items sorted by `less`: the item equivalent to `key` (neither less than
the other), if any. -/
def btFind (k : V) : List V → Option V
  | [] => none
  | w :: ws => if less w k then btFind k ws else if less k w then none else some w

/-- `ReplaceOrInsert(v)` on items sorted by `less`: the item equivalent to `v` is replaced
by `v`, or `v` is inserted at its sorted position. -/
def btInsert (v : V) : List V → List V
  | [] => [v]
  | w :: ws => if less w v then w :: btInsert v ws else if less v w then v :: w :: ws else v :: ws

/-- `Delete(key)` on items sorted by `less`: the item equivalent to `key` is removed, if
any. -/
def btDelete (k : V) : List V → List V
  | [] => []
  | w :: ws => if less w k then w :: btDelete k ws else if less k w then w :: ws else ws

/-- The items `AscendGreaterOrEqual(pivot, _)` visits, in order: those not less than
`pivot`. -/
abbrev btAscendGe (pivot : V) (items : List V) : List V :=
  items.filter (fun v => !decide (less v pivot))

/-- The items `AscendRange(ge, lt, _)` visits, in order: those not less than `ge` and less
than `lt`. -/
abbrev btAscendRange (ge lt : V) (items : List V) : List V :=
  items.filter (fun v => !decide (less v ge) && decide (less v lt))

end ops

/-! ## Lemmas -/

section lemmas
variable {V : Type} {less : V → V → Prop} [DecidableRel less]

theorem btInsert_mem {v : V} {items : List V} {x : V} (h : x ∈ btInsert less v items) :
    x = v ∨ x ∈ items := by
  induction items with
  | nil => simp [btInsert] at h; exact Or.inl h
  | cons w ws ih =>
    unfold btInsert at h
    split at h
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inr (h ▸ List.mem_cons_self)
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · split at h
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem btDelete_sublist (k : V) (items : List V) : (btDelete less k items).Sublist items := by
  induction items with
  | nil => simp [btDelete]
  | cons w ws ih =>
    unfold btDelete
    split
    · exact ih.cons_cons w
    · split
      · exact List.Sublist.refl _
      · exact List.sublist_cons_self w ws

theorem btDelete_mem {k : V} {items : List V} {x : V} (h : x ∈ btDelete less k items) :
    x ∈ items :=
  (btDelete_sublist k items).subset h

theorem btFind_mem {k : V} {items : List V} {x : V} (h : btFind less k items = some x) :
    x ∈ items := by
  induction items with
  | nil => simp [btFind] at h
  | cons w ws ih =>
    unfold btFind at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · split at h
      · simp at h
      · simp at h; exact h ▸ List.mem_cons_self

/-- What `btFind` returns is equivalent to the key. -/
theorem btFind_equiv {k : V} {items : List V} {x : V} (h : btFind less k items = some x) :
    ¬ less x k ∧ ¬ less k x := by
  induction items with
  | nil => simp [btFind] at h
  | cons w ws ih =>
    unfold btFind at h
    split at h
    · exact ih h
    · split at h
      · simp at h
      · simp at h; subst h; exact ⟨‹_›, ‹_›⟩

/-- `ReplaceOrInsert` keeps the items sorted. -/
theorem btInsert_sorted (hord : StrictWeakOrder less) {v : V} {items : List V}
    (h : items.Pairwise less) : (btInsert less v items).Pairwise less := by
  induction items with
  | nil => simp [btInsert]
  | cons w ws ih =>
    rw [List.pairwise_cons] at h
    unfold btInsert
    split
    · rename_i hwv
      rw [List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih h.2⟩
      rcases btInsert_mem hx with rfl | hx
      · exact hwv
      · exact h.1 x hx
    · split
      · rename_i _ hvw
        rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, List.pairwise_cons.2 h⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hvw
        · exact hord.trans _ _ _ hvw (h.1 x hx)
      · rename_i hwv hvw
        rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, h.2⟩
        have hwx := h.1 x hx
        refine Classical.byContradiction fun hvx => ?_
        by_cases hxv : less x v
        · exact hwv (hord.trans _ _ _ hwx hxv)
        · exact (hord.incomp_trans w v x hwv hvw hvx hxv).1 hwx

/-- `Delete` keeps the items sorted. -/
theorem btDelete_sorted {k : V} {items : List V} (h : items.Pairwise less) :
    (btDelete less k items).Pairwise less :=
  h.sublist (btDelete_sublist k items)

end lemmas

/-! ## The predicate, from the btree's proof

The btree's own predicate (`btree.ownBTree`, `Proof/k8s_io/.../btree/Defs.lean`) orders
*keys* under a strict total order, with a persistent relation between an item and its key.
The store's view orders *models* `V` under a strict weak order `less` (an entry is a key
and a value, ordered by key). The bridge takes as keys the classes of `less`'s
incomparability (`Key`), on which `less` is a strict total order (`keyOrder`), and
pairs each Go item with its model (`zs`, the btree's entries being `zs.map entry`), every
pair related by `isItem`. -/

section key
variable {V : Type} (less : V → V → Prop)

/-- Incomparability: neither is less than the other ("equal" items). -/
def incomp (a b : V) : Prop := ¬ less a b ∧ ¬ less b a

variable {less}

/-- Incomparability of a strict weak order is an equivalence. -/
def keySetoid (h : StrictWeakOrder less) : Setoid V where
  r := incomp less
  iseqv := ⟨fun a => ⟨h.irrefl a, h.irrefl a⟩, fun hab => ⟨hab.2, hab.1⟩,
    fun hab hbc => h.incomp_trans _ _ _ hab.1 hab.2 hbc.1 hbc.2⟩

/-- The keys: the classes of incomparable items. -/
def Key (h : StrictWeakOrder less) : Type := Quotient (keySetoid h)

/-- The class of an item. -/
def key (h : StrictWeakOrder less) (v : V) : Key h := Quotient.mk (keySetoid h) v

/-- `less` respects incomparability. -/
theorem less_congr (h : StrictWeakOrder less) {a1 b1 a2 b2 : V} (ha : incomp less a1 a2)
    (hb : incomp less b1 b2) (hl : less a1 b1) : less a2 b2 := by
  -- first move the left argument, then the right one
  have h1 : less a2 b1 := by
    refine Classical.byContradiction fun h21 => ?_
    by_cases h12 : less b1 a2
    · exact ha.1 (h.trans _ _ _ hl h12)
    · exact (h.incomp_trans a1 a2 b1 ha.1 ha.2 h21 h12).1 hl
  refine Classical.byContradiction fun h22 => ?_
  by_cases h22' : less b2 a2
  · exact hb.2 (h.trans _ _ _ h22' h1)
  · exact (h.incomp_trans a2 b2 b1 h22 h22' hb.2 hb.1).1 h1

/-- `less` on classes. -/
def keyLt (h : StrictWeakOrder less) : Key h → Key h → Prop :=
  Quotient.lift₂ (s₁ := keySetoid h) (s₂ := keySetoid h) less (by
    intro a1 b1 a2 b2 ha hb
    exact propext ⟨less_congr h ha hb,
      less_congr h ⟨ha.2, ha.1⟩ ⟨hb.2, hb.1⟩⟩)

theorem keyLt_key (h : StrictWeakOrder less) (a b : V) :
    keyLt h (key h a) (key h b) ↔ less a b := Iff.rfl

theorem key_eq_iff (h : StrictWeakOrder less) (a b : V) :
    key h a = key h b ↔ incomp less a b :=
  ⟨fun e => Quotient.exact (s := keySetoid h) e, fun e => Quotient.sound (s := keySetoid h) e⟩

theorem keyLt_order (h : StrictWeakOrder less) : btree.StrictOrder (keyLt h) where
  irrefl := by
    intro a; induction a using Quotient.ind; exact h.irrefl _
  trans := by
    intro a b c; induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind; exact h.trans _ _ _
  total := by
    intro a b; induction a using Quotient.ind; induction b using Quotient.ind
    rename_i a b
    by_cases hab : less a b
    · exact Or.inl hab
    by_cases hba : less b a
    · exact Or.inr (Or.inr hba)
    exact Or.inr (Or.inl ((key_eq_iff h a b).2 ⟨hab, hba⟩))

end key

/-! ### Entries: a Go item with its model

The bridge keeps the list `zs` of pairs (Go item, model): the btree's entries are
`zs.map (entry h)` and the models `zs.map Prod.snd`. -/

section entries

theorem ite_pos {α : Type _} {c : Prop} [Decidable c] {a b : α} (hc : c) :
    (if c then a else b) = a := by simp [hc]

theorem ite_neg {α : Type _} {c : Prop} [Decidable c] {a b : α} (hc : ¬ c) :
    (if c then a else b) = b := by simp [hc]

variable {T' V : Type} {less : V → V → Prop} (h : StrictWeakOrder less) [DecidableRel less]

/-- The btree's entry of a Go item with its model: the item and the model's class. -/
def entry (z : T' × V) : T' × Key h := (z.1, key h z.2)

/-- `btInsert` on pairs (by the model). -/
def pInsert (z0 : T' × V) : List (T' × V) → List (T' × V)
  | [] => [z0]
  | w :: ws => if less w.2 z0.2 then w :: pInsert z0 ws
    else if less z0.2 w.2 then z0 :: w :: ws else z0 :: ws

omit [DecidableRel less] in
theorem sorted_entries (zs : List (T' × V)) :
    btree.Sorted (keyLt h) (zs.map (entry h)) ↔ (zs.map Prod.snd).Pairwise less := by
  unfold btree.Sorted
  rw [List.pairwise_map, List.pairwise_map]
  rfl

variable {h}

theorem pInsert_snd (z0 : T' × V) (zs : List (T' × V)) :
    (pInsert (less := less) z0 zs).map Prod.snd = btInsert less z0.2 (zs.map Prod.snd) := by
  induction zs with
  | nil => simp [pInsert, btInsert]
  | cons w ws ih =>
    simp only [pInsert, btInsert, List.map_cons]
    split
    · simp [ih]
    · split <;> simp

open Classical in
theorem pInsert_entries (z0 : T' × V) (zs : List (T' × V)) :
    (pInsert (less := less) z0 zs).map (entry h) =
      btree.insert (keyLt h) (zs.map (entry h)) (entry h z0) := by
  induction zs with
  | nil => simp [pInsert, btree.insert]
  | cons w ws ih =>
    simp only [pInsert, List.map_cons]
    rw [btree.insert]
    have hlt : keyLt h (entry h z0).2 (entry h w).2 ↔ less z0.2 w.2 := Iff.rfl
    have heq : (entry h z0).2 = (entry h w).2 ↔ incomp less z0.2 w.2 := key_eq_iff h _ _
    by_cases h1 : less w.2 z0.2
    · have h2 : ¬ less z0.2 w.2 := fun h2 => h.irrefl _ (h.trans _ _ _ h1 h2)
      rw [ite_pos h1, ite_neg ((not_congr hlt).2 h2), ite_neg ((not_congr heq).2 (fun e => e.2 h1)), List.map_cons, ih]
    · rw [ite_neg h1]
      by_cases h2 : less z0.2 w.2
      · rw [ite_pos h2, ite_pos (hlt.2 h2)]; rfl
      · rw [ite_neg h2, ite_neg ((not_congr hlt).2 h2), ite_pos (heq.2 ⟨h2, h1⟩)]; rfl

theorem pInsert_mem {z0 z : T' × V} {zs : List (T' × V)} (hz : z ∈ pInsert (less := less) z0 zs) :
    z = z0 ∨ z ∈ zs := by
  induction zs with
  | nil => simp [pInsert] at hz; exact Or.inl hz
  | cons w ws ih =>
    simp only [pInsert] at hz
    split at hz
    · rcases List.mem_cons.1 hz with hz | hz
      · exact Or.inr (hz ▸ List.mem_cons_self)
      · rcases ih hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (List.mem_cons_of_mem _ hz)
    · split at hz
      · rcases List.mem_cons.1 hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr hz
      · rcases List.mem_cons.1 hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (List.mem_cons_of_mem _ hz)

open Classical in
omit [DecidableRel less] in
/-- The btree's `lookup` on the entries: the first pair whose model is equivalent. -/
theorem lookup_entries (zs : List (T' × V)) (k : V) :
    btree.lookup (zs.map (entry h)) (key h k) =
      (zs.find? (fun z => decide (key h z.2 = key h k))).map Prod.fst := by
  unfold btree.lookup
  rw [List.find?_map, Option.map_map]
  rfl

open Classical in
/-- `btFind` on sorted models: the first equivalent one. -/
theorem btFind_eq_find (zs : List (T' × V)) (k : V) (hs : (zs.map Prod.snd).Pairwise less) :
    btFind less k (zs.map Prod.snd) =
      (zs.find? (fun z => decide (key h z.2 = key h k))).map Prod.snd := by
  induction zs with
  | nil => simp [btFind]
  | cons w ws ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hs
    simp only [List.map_cons, btFind, List.find?_cons]
    by_cases h1 : less w.2 k
    · rw [ite_pos h1, ih hs.2]
      have : ¬ key h w.2 = key h k := fun e => ((key_eq_iff h _ _).1 e).1 h1
      simp [this]
    · rw [ite_neg h1]
      by_cases h2 : less k w.2
      · rw [ite_pos h2]
        have : ¬ key h w.2 = key h k := fun e => ((key_eq_iff h _ _).1 e).2 h2
        simp only [this, decide_false]
        rw [List.find?_eq_none.2]
        · rfl
        · intro z hz
          have hwz := hs.1 z.2 ⟨z, hz, rfl⟩
          simp only [decide_eq_true_eq]
          exact fun e => ((key_eq_iff h _ _).1 e).2 (h.trans _ _ _ h2 hwz)
      · rw [ite_neg h2]
        have : key h w.2 = key h k := (key_eq_iff h _ _).2 ⟨h1, h2⟩
        simp [this]

open Classical in
/-- The pairs left by `Delete(k)`. -/
def pDelete (zs : List (T' × V)) (k : V) : List (T' × V) :=
  zs.filter (fun z => decide (key h z.2 ≠ key h k))

omit [DecidableRel less] in
theorem pDelete_entries (zs : List (T' × V)) (k : V) :
    (pDelete (h := h) zs k).map (entry h) = btree.delete (zs.map (entry h)) (key h k) := by
  unfold pDelete btree.delete
  rw [List.filter_map]
  rfl

theorem pDelete_snd (zs : List (T' × V)) (k : V) (hs : (zs.map Prod.snd).Pairwise less) :
    (pDelete (h := h) zs k).map Prod.snd = btDelete less k (zs.map Prod.snd) := by
  unfold pDelete
  induction zs with
  | nil => simp [btDelete]
  | cons w ws ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hs
    simp only [List.map_cons, btDelete, List.filter_cons]
    have hall : ∀ z ∈ ws, less k z.2 → ¬ key h z.2 = key h k := fun z _ hk e =>
      ((key_eq_iff h _ _).1 e).2 hk
    by_cases h1 : less w.2 k
    · rw [ite_pos h1, ← ih hs.2]
      have : ¬ key h w.2 = key h k := fun e => ((key_eq_iff h _ _).1 e).1 h1
      simp [this]
    · rw [ite_neg h1]
      by_cases h2 : less k w.2
      · rw [ite_pos h2]
        have : ¬ key h w.2 = key h k := fun e => ((key_eq_iff h _ _).1 e).2 h2
        simp only [this, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons]
        rw [List.filter_eq_self.2]
        intro z hz
        simpa using hall z hz (h.trans _ _ _ h2 (hs.1 z.2 ⟨z, hz, rfl⟩))
      · rw [ite_neg h2]
        have hwk : key h w.2 = key h k := (key_eq_iff h _ _).2 ⟨h1, h2⟩
        simp only [hwk, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [List.filter_eq_self.2]
        intro z hz
        have hwz := hs.1 z.2 ⟨z, hz, rfl⟩
        have hkz : less k z.2 :=
          less_congr h ((key_eq_iff h _ _).1 hwk) ⟨h.irrefl _, h.irrefl _⟩ hwz
        simpa using hall z hz hkz

omit [DecidableRel less] in
theorem ascRange_ge_entries [DecidableRel less] (zs : List (T' × V)) (vp : V) :
    btree.ascRange (keyLt h) (zs.map (entry h)) (some (key h vp)) none =
      (zs.filter (fun z => !decide (less z.2 vp))).map (entry h) := by
  unfold btree.ascRange
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro z _
  have hi : btree.ascIn (keyLt h) (some (key h vp)) none (key h z.2) ↔ ¬ less z.2 vp :=
    ⟨fun H => H.1 _ rfl, fun H => ⟨fun a ha => by cases ha; exact H, fun b hb => by cases hb⟩⟩
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, entry, decide_eq_true_iff, hi, Bool.not_eq_true',
    decide_eq_false_iff_not]

theorem btAscendGe_entries (zs : List (T' × V)) (vp : V) :
    btAscendGe less vp (zs.map Prod.snd) =
      (zs.filter (fun z => !decide (less z.2 vp))).map Prod.snd := by
  unfold btAscendGe
  rw [List.filter_map]
  rfl

omit [DecidableRel less] in
theorem ascRange_range_entries [DecidableRel less] (zs : List (T' × V)) (vge vlt : V) :
    btree.ascRange (keyLt h) (zs.map (entry h)) (some (key h vge)) (some (key h vlt)) =
      (zs.filter (fun z => !decide (less z.2 vge) && decide (less z.2 vlt))).map (entry h) := by
  unfold btree.ascRange
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro z _
  have hi : btree.ascIn (keyLt h) (some (key h vge)) (some (key h vlt)) (key h z.2) ↔
      ¬ less z.2 vge ∧ less z.2 vlt :=
    ⟨fun H => ⟨H.1 _ rfl, H.2 _ rfl⟩,
      fun H => ⟨fun a ha => by cases ha; exact H.1, fun b hb => by cases hb; exact H.2⟩⟩
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, entry, decide_eq_true_iff, hi, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not]

theorem btAscendRange_entries (zs : List (T' × V)) (vge vlt : V) :
    btAscendRange less vge vlt (zs.map Prod.snd) =
      (zs.filter (fun z => !decide (less z.2 vge) && decide (less z.2 vlt))).map Prod.snd := by
  unfold btAscendRange
  rw [List.filter_map]
  rfl

end entries

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {T' : Type} {V : Type}

/-- The btree's item order for models `V` under `less`: keys are classes, and a Go item
has the class of a model it has (`isItem`). -/
def keyOrder (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    {less : V → V → Prop} (h : StrictWeakOrder less) : btree.ItemOrder GF T' (Key h) where
  lt := keyLt h
  order := keyLt_order h
  item p k := iprop(∃ v, isItem p v ∗ ⌜key h v = k⌝)
  item_persistent _ _ := by infer_instance

/-- `ownBTree T t isItem less items dq`: `t` is a `*btree.BTree[T]` (Lean representation
`T'` of the Go type `T`) holding, in order, Go items modelling `items` (by `isItem`), with
the `LessFunc` it was created with deciding the strict weak order `less`; at fraction
`dq` (`DFrac.own 1` to write, any fraction to read, `DFrac.discard` for a read-only tree
shared for good). The btree's own `btree.ownBTree` on the classes of the models: `zs`
pairs each Go item with its model (`entry`). -/
def ownBTree {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) (items : List V) (dq : DFrac) : IProp GF :=
  iprop(∃ (h : StrictWeakOrder less) (zs : List (T' × V)),
    btree.ownBTree (keyOrder isItem h) t dq (zs.map (entry h)) ∗
    ⌜zs.map Prod.snd = items⌝ ∗
    □ (∀ z, ⌜z ∈ zs⌝ -∗ isItem z.1 z.2))

instance ownBTree_persistent {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) (items : List V) [k8s_io.utils.third_party.forked.golang.btree.Assumptions] :
    Persistent (ownBTree T t isItem less items DFrac.discard) := by
  unfold ownBTree; infer_instance

/-- Make an owned tree read-only for good (`ownBTree … dq ==∗ ownBTree … discard`). -/
theorem ownBTree_persist {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) (items : List V) (dq : DFrac)
    [k8s_io.utils.third_party.forked.golang.btree.Assumptions] :
    ownBTree T t isItem less items dq ⊢ |==> ownBTree T t isItem less items DFrac.discard := by
  unfold ownBTree
  iintro ⟨%h, %zs, Ht, %Hzs, #Hall⟩
  imod btree.ownBTree_persist _ t dq _ $$ Ht with Ht
  imodintro
  iexists h, zs
  iframe # ∗
  ipureintro; exact Hzs

theorem keyOrder_item (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    {less : V → V → Prop} (h : StrictWeakOrder less) (p : T') (v : V) :
    isItem p v ⊢ (keyOrder isItem h).item p (key h v) := by
  show isItem p v ⊢ iprop(∃ w, isItem p w ∗ ⌜key h w = key h v⌝)
  iintro H
  iexists v; iframe H; ipureintro; rfl

theorem keyOrder_item_eq (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    {less : V → V → Prop} (h : StrictWeakOrder less) (p : T') (k : Key h) :
    (keyOrder isItem h).item p k = iprop(∃ v, isItem p v ∗ ⌜key h v = k⌝) := rfl

/-- The btree's entries are sorted. -/
theorem btree_ownBTree_sorted {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (o : btree.ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) :
    btree.ownBTree o t dq s ⊢ btree.ownBTree o t dq s ∗ ⌜btree.Sorted o.lt s⌝ := by
  unfold btree.ownBTree
  iintro H
  iNamed H
  isplitl
  · iexists tv, f, less, d; iframe Ht Hroot Hcow Hitems; ipureintro; exact ⟨Hdeg, Hlen, Hsorted⟩
  · ipureintro; exact Hsorted

variable {T' : Type} {V : Type}

/-- The triple of the `LessFunc[T]` closure `f` given to `New`: on items modelling `va`
and `vb`, it returns whether `less va vb`. (Items are persistent, so nothing is given
back.) -/
def btLessSpec (f : GoFunc) (isItem : T' → V → IProp GF)
    (less : V → V → Prop) [DecidableRel less] : IProp GF :=
  iprop(∀ (a b : T') (va vb : V),
    {{ isItem a va ∗ isItem b vb }}
      (App (App (Val #f) (Val #a)) (Val #b))
    {{ RET #(decide (less va vb)); True }})

instance btLessSpec_persistent (f : GoFunc) (isItem : T' → V → IProp GF)
    (less : V → V → Prop) [DecidableRel less] : Persistent (btLessSpec f isItem less) := by
  unfold btLessSpec; infer_instance

/-- The triple of an `ItemIterator[T]` closure `iter` the `Ascend*` methods call on the
visited items `vis`, in loop-invariant style (as the ring buffer's `iterSpec`): called on
the `i`-th visited item (a Go item `p` modelling it) with `P i`, it returns whether to go
on, with `P (i + 1)` if so and the final postcondition `Q` if not. -/
def btIterSpec (iter : GoFunc) (isItem : T' → V → IProp GF) (vis : List V)
    (P : Nat → IProp GF) (Q : IProp GF) : IProp GF :=
  iprop(∀ (i : Nat) (p : T') (v : V), ⌜vis[i]? = some v⌝ -∗
    {{ P i ∗ isItem p v }}
      (App (Val #iter) (Val #p))
    {{ (cont : Bool), RET #cont; if cont then P (i + 1) else Q }})

instance btIterSpec_persistent (iter : GoFunc) (isItem : T' → V → IProp GF) (vis : List V)
    (P : Nat → IProp GF) (Q : IProp GF) : Persistent (btIterSpec iter isItem vis P Q) := by
  unfold btIterSpec; infer_instance

/-- The btree's iterator protocol from the model's `btIterSpec`, for an iteration
visiting the pairs `zs'` (taken from `zs`, whose items all model their models). -/
theorem iterProtocol_of_btIterSpec [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    {less : V → V → Prop} (h : StrictWeakOrder less) (zs zs' : List (T' × V))
    (hsub : ∀ z ∈ zs', z ∈ zs) (iter : GoFunc) (P : Nat → IProp GF) (Q : IProp GF)
    (vis : List V) (hvis : vis = zs'.map Prod.snd)
    (r : List (T' × Key h)) (hr : r = zs'.map (entry h)) :
    iprop(□ (∀ z, ⌜z ∈ zs⌝ -∗ isItem z.1 z.2)) ∗ btIterSpec iter isItem vis P Q ⊢
      btree.iterProtocol (keyOrder isItem h) iter r
        (fun pre b => if b then Q else P pre.length) := by
  subst hvis hr
  unfold btree.iterProtocol btIterSpec
  iintro ⟨#Hall, #Hit⟩
  imodintro
  iintro %pre %e %Hpre
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨l, hl⟩ := Hpre
  have hget : (zs'.map (entry h))[pre.length]? = some e := by rw [← hl]; simp
  rw [List.getElem?_map, Option.map_eq_some_iff] at hget
  obtain ⟨z, hz, rfl⟩ := hget
  simp only [entry]
  have hvis : (zs'.map Prod.snd)[pre.length]? = some z.2 := by
    rw [List.getElem?_map, hz]; rfl
  have hmem : z ∈ zs := hsub z (List.mem_of_getElem? hz)
  ihave Hc := Hit $$ %(pre.length) %z.1 %z.2 %hvis
  wp_start_folded as ⟨HP, -⟩
  iapply Hc $$ [HP]
  · iframe HP; iapply Hall; ipureintro; exact hmem
  inext
  iintro %cont
  cases cont
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro Hcont; iapply HΦ; simp only [Bool.not_false, ↓reduceIte]; iexact Hcont
  · simp only [↓reduceIte]
    iintro Hcont; iapply HΦ
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add]
    iexact Hcont

/-- What the btree's iteration ends with, in the model's terms. -/
theorem iterDone_model {K : Type} (r : List (T' × K)) (P : Nat → IProp GF) (Q : IProp GF)
    (vis : List V) (hlen : vis.length = r.length) :
    btree.iterDone r (fun pre b => if b then Q else P pre.length) ⊢ iprop(Q ∨ P vis.length) := by
  unfold btree.iterDone
  refine exists_elim fun pre => exists_elim fun stopped => ?_
  cases stopped
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨HP, %Hp⟩
    iright
    rw [hlen, ← Hp.2 (by simp)]
    iexact HP
  · simp only [↓reduceIte]
    iintro ⟨HQ, -⟩
    ileft; iexact HQ

end defs

/-! ## The store's view of the btree's methods

The triples the store's proofs use, on the predicate above (they were this package's
trust boundary until the btree was proved): each is derived from the btree method's own
spec (`Spec/k8s_io/.../btree/`), as `<fn>.modelSpec_of`. -/

section model
open go_etcd_io.etcd.cache.v3 k8s_io.utils.third_party.forked.golang

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `btree.New[T](degree, less)` (`New` → `NewWithFreeList(degree, less,
NewFreeList(DefaultFreeListSize))`): an empty tree, for `1 < degree <= 2^62` (Go panics with "bad
degree" below; above, `maxItems() = 2·degree - 1` overflows and the second insert
panics) and a `LessFunc` closure `less` deciding a strict weak order
`lessR` (`btLessSpec`; Go's documentation: "It should implement a strict ordering"). -/
def btree.New.modelSpec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (degree : w64) (less : GoFunc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (lessR : V → V → Prop) [DecidableRel lessR],
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜1 < sint.Z degree ∧ sint.Z degree ≤ 2 ^ 62⌝ ∗ ⌜StrictWeakOrder lessR⌝ ∗ btLessSpec less isItem lessR }}
    (App (App (Val #(functions btree.New [T])) (Val #degree)) (Val #less))
  {{ (t : Loc), RET #t; EtcdGrove.ownBTree T t isItem lessR [] (DFrac.own 1) }}

/-- `t.ReplaceOrInsert(item)`: Go's documentation: "ReplaceOrInsert adds the given item to
the tree. If an item in the tree already equals the given one, it is removed from the
tree and returned, and the second return value is true. Otherwise, (zeroValue, false)."
On a fully owned tree: the items become `btInsert` (the equivalent item replaced, or `v`
inserted in order), and the replaced one (`btFind`) is returned. -/
def btree.BTree.ReplaceOrInsert.modelSpec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (item : T') (v : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ EtcdGrove.ownBTree T t isItem less items (DFrac.own 1) ∗ isItem item v }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"ReplaceOrInsert")) (Val #item))
  {{ (old : T') (ok : Bool), RET (PairV #old #ok);
      EtcdGrove.ownBTree T t isItem less (btInsert less v items) (DFrac.own 1) ∗
      match btFind less v items with
      | some w => ⌜ok = true⌝ ∗ isItem old w
      | none => ⌜ok = false ∧ old = zero_val T'⌝ }}

/-- `t.Get(key)`: Go's documentation: "Get looks for the key item in the tree, returning
it. It returns (zeroValue, false) if unable to find that item." The item found is the one
equivalent to `key` (`btFind`); a read, on any fraction. -/
def btree.BTree.Get.modelSpec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (dq : DFrac) (key : T') (k : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ EtcdGrove.ownBTree T t isItem less items dq ∗ isItem key k }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"Get")) (Val #key))
  {{ (item : T') (ok : Bool), RET (PairV #item #ok);
      EtcdGrove.ownBTree T t isItem less items dq ∗
      match btFind less k items with
      | some v => ⌜ok = true⌝ ∗ isItem item v
      | none => ⌜ok = false ∧ item = zero_val T'⌝ }}

/-- `t.Delete(key)`: Go's documentation: "Delete removes an item equal to the passed in
item from the tree, returning it. If no such item exists, returns (zeroValue, false)." On a
fully owned tree: the items become `btDelete`, and the removed one (`btFind`) is
returned. -/
def btree.BTree.Delete.modelSpec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (key : T') (k : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ EtcdGrove.ownBTree T t isItem less items (DFrac.own 1) ∗ isItem key k }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"Delete")) (Val #key))
  {{ (old : T') (ok : Bool), RET (PairV #old #ok);
      EtcdGrove.ownBTree T t isItem less (btDelete less k items) (DFrac.own 1) ∗
      match btFind less k items with
      | some w => ⌜ok = true⌝ ∗ isItem old w
      | none => ⌜ok = false ∧ old = zero_val T'⌝ }}

/-- `t.Clone()`: Go's documentation: "Clone clones the btree, lazily. Clone should not be
called concurrently, but the original tree (t) and the new tree (t2) can be used
concurrently once the Clone call completes." Clone writes `t` (its copy-on-write context),
so it takes the tree fully owned; it gives two fully owned trees with the same items
(copy-on-write keeps them independent). -/
def btree.BTree.Clone.modelSpec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ EtcdGrove.ownBTree T t isItem less items (DFrac.own 1) }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"Clone")) (Val #()))
  {{ (t2 : Loc), RET #t2;
      EtcdGrove.ownBTree T t isItem less items (DFrac.own 1) ∗ EtcdGrove.ownBTree T t2 isItem less items (DFrac.own 1) }}

/-- `t.AscendGreaterOrEqual(pivot, iter)`: Go's documentation: "AscendGreaterOrEqual calls
the iterator for every value in the tree within the range [pivot, last], until iterator
returns false." The visited items are `btAscendGe` (those not less than `pivot`, in order);
with `iter` meeting `btIterSpec` for an invariant `P` and a final postcondition `Q`: `Q`
if `iter` stopped the iteration, `P` of the number of visited items if not. A read, on any
fraction. -/
def btree.BTree.AscendGreaterOrEqual.modelSpec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (dq : DFrac)
    (pivot : T') (vp : V) (iter : GoFunc) (P : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ EtcdGrove.ownBTree T t isItem less items dq ∗ isItem pivot vp ∗ P 0 ∗
      btIterSpec iter isItem (btAscendGe less vp items) P Q }}
    (App (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"AscendGreaterOrEqual")) (Val #pivot)) (Val #iter))
  {{ RET #(); EtcdGrove.ownBTree T t isItem less items dq ∗
      (Q ∨ P (btAscendGe less vp items).length) }}

/-- `t.AscendRange(greaterOrEqual, lessThan, iter)`: Go's documentation: "AscendRange
calls the iterator for every value in the tree within the range [greaterOrEqual,
lessThan), until iterator returns false." The visited items are `btAscendRange` (those
not less than `greaterOrEqual` and less than `lessThan`, in order), in the loop-invariant
style of `AscendGreaterOrEqual`. A read, on any fraction. -/
def btree.BTree.AscendRange.modelSpec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (dq : DFrac)
    (ge lt : T') (vge vlt : V) (iter : GoFunc) (P : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ EtcdGrove.ownBTree T t isItem less items dq ∗ isItem ge vge ∗
      isItem lt vlt ∗ P 0 ∗ btIterSpec iter isItem (btAscendRange less vge vlt items) P Q }}
    (App (App (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"AscendRange")) (Val #ge)) (Val #lt)) (Val #iter))
  {{ RET #(); EtcdGrove.ownBTree T t isItem less items dq ∗
      (Q ∨ P (btAscendRange less vge vlt items).length) }}

open Classical in
theorem btree.New.modelSpec_of (wp : btree.New.spec (GF := GF) (hG := hG)) :
    btree.New.modelSpec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V degree less isItem _ lessR _
  wp_start_folded as ⟨%Hdeg, %Hswo, #Hless⟩
  iapply wp (keyOrder isItem Hswo) degree less Hdeg.1 Hdeg.2 $$ []
  · iframe #
    unfold btree.isLess btLessSpec
    iintro %a %b %ka %kb
    rw [keyOrder_item_eq, keyOrder_item_eq]
    wp_start_folded as ⟨Ha, Hb⟩
    icases Ha with ⟨%va, Ha, %Hka⟩
    icases Hb with ⟨%vb, Hb, %Hkb⟩
    iapply Hless $$ [Ha Hb]
    · iframe
    inext
    iintro -
    iapply HΦ
    ipureintro
    subst Hka Hkb
    exact decide_eq_true_iff
  inext
  iintro %t Ht
  iapply HΦ
  unfold EtcdGrove.ownBTree
  iexists Hswo, []
  simp only [List.map_nil]
  iframe Ht
  isplitr
  · ipureintro; simp
  · imodintro; iintro %z %hz; simp at hz

open Classical in
theorem btree.BTree.ReplaceOrInsert.modelSpec_of (wp : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG)) :
    btree.BTree.ReplaceOrInsert.modelSpec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V t isItem _ less _ items item v
  wp_start_folded as ⟨%Hswo, Ht, #Hv⟩
  unfold EtcdGrove.ownBTree
  icases Ht with ⟨%h, %zs, Ht, %Hzs, #Hall⟩
  icases btree_ownBTree_sorted _ _ _ _ $$ Ht with ⟨Ht, %Hsorted⟩
  iapply wp (keyOrder isItem h) t (zs.map (entry h)) item (EtcdGrove.key h v) $$ [Ht]
  · iframe # ∗
    iapply keyOrder_item; iexact Hv
  inext
  iintro Ht
  iapply HΦ
  subst Hzs
  isplitl [Ht]
  · iexists h, pInsert (item, v) zs
    rw [show btree.insert (keyOrder isItem h).lt (zs.map (entry h)) (item, EtcdGrove.key h v) =
      (pInsert (item, v) zs).map (entry h) from (pInsert_entries (h := h) (item, v) zs).symm]
    iframe Ht
    isplitr
    · ipureintro; exact pInsert_snd _ _
    · imodintro; iintro %z %hz
      rcases pInsert_mem hz with rfl | hz
      · iexact Hv
      · iapply Hall; ipureintro; exact hz
  have Hpw := (sorted_entries h zs).1 Hsorted
  rw [btFind_eq_find (h := h) zs v Hpw, lookup_entries]
  cases hf : zs.find? (fun z => decide (EtcdGrove.key h z.2 = EtcdGrove.key h v)) with
  | none => simp only [Option.map_none, Option.getD_none, Option.isSome_none]; ipureintro; simp
  | some z =>
    simp only [Option.map_some, Option.getD_some, Option.isSome_some]
    isplitl []
    · ipureintro; simp
    · iapply Hall; ipureintro; exact List.mem_of_find?_eq_some hf

open Classical in
theorem btree.BTree.Get.modelSpec_of (wp : btree.BTree.Get.spec (GF := GF) (hG := hG)) :
    btree.BTree.Get.modelSpec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V t isItem _ less _ items dq key k
  wp_start_folded as ⟨%Hswo, Ht, #Hk⟩
  unfold EtcdGrove.ownBTree
  icases Ht with ⟨%h, %zs, Ht, %Hzs, #Hall⟩
  icases btree_ownBTree_sorted _ _ _ _ $$ Ht with ⟨Ht, %Hsorted⟩
  iapply wp (keyOrder isItem h) t dq (zs.map (entry h)) key (EtcdGrove.key h k) $$ [Ht]
  · iframe # ∗
    iapply keyOrder_item; iexact Hk
  inext
  iintro Ht
  iapply HΦ
  isplitl [Ht]
  · iexists h, zs; iframe # ∗; ipureintro; exact Hzs
  subst Hzs
  have Hpw := (sorted_entries h zs).1 Hsorted
  rw [btFind_eq_find (h := h) zs k Hpw]
  rw [lookup_entries]
  cases hf : zs.find? (fun z => decide (EtcdGrove.key h z.2 = EtcdGrove.key h k)) with
  | none => simp only [Option.map_none, Option.getD_none, Option.isSome_none]; ipureintro; simp
  | some z =>
    simp only [Option.map_some, Option.getD_some, Option.isSome_some]
    isplitl []
    · ipureintro; simp
    · iapply Hall; ipureintro; exact List.mem_of_find?_eq_some hf

open Classical in
theorem btree.BTree.Delete.modelSpec_of (wp : btree.BTree.Delete.spec (GF := GF) (hG := hG)) :
    btree.BTree.Delete.modelSpec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V t isItem _ less _ items key k
  wp_start_folded as ⟨%Hswo, Ht, #Hk⟩
  unfold EtcdGrove.ownBTree
  icases Ht with ⟨%h, %zs, Ht, %Hzs, #Hall⟩
  icases btree_ownBTree_sorted _ _ _ _ $$ Ht with ⟨Ht, %Hsorted⟩
  iapply wp (keyOrder isItem h) t (zs.map (entry h)) key (EtcdGrove.key h k) $$ [Ht]
  · iframe # ∗
    iapply keyOrder_item; iexact Hk
  inext
  iintro Ht
  iapply HΦ
  subst Hzs
  simp only [btree.removeOp]
  isplitl [Ht]
  · iexists h, pDelete (h := h) zs k
    rw [show btree.delete (zs.map (entry h)) (EtcdGrove.key h k) =
      (pDelete (h := h) zs k).map (entry h) from (pDelete_entries (h := h) zs k).symm]
    iframe Ht
    isplitr
    · ipureintro; exact pDelete_snd _ _ ((sorted_entries h zs).1 Hsorted)
    · imodintro; iintro %z %hz
      iapply Hall; ipureintro; exact (List.mem_filter.1 hz).1
  have Hpw := (sorted_entries h zs).1 Hsorted
  rw [btFind_eq_find (h := h) zs k Hpw, lookup_entries]
  cases hf : zs.find? (fun z => decide (EtcdGrove.key h z.2 = EtcdGrove.key h k)) with
  | none => simp only [Option.map_none, Option.getD_none, Option.isSome_none]; ipureintro; simp
  | some z =>
    simp only [Option.map_some, Option.getD_some, Option.isSome_some]
    isplitl []
    · ipureintro; simp
    · iapply Hall; ipureintro; exact List.mem_of_find?_eq_some hf

open Classical in
theorem btree.BTree.Clone.modelSpec_of (wp : btree.BTree.Clone.spec (GF := GF) (hG := hG)) :
    btree.BTree.Clone.modelSpec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V t isItem _ less _ items
  wp_start_folded as ⟨%Hswo, Ht⟩
  unfold EtcdGrove.ownBTree
  icases Ht with ⟨%h, %zs, Ht, %Hzs, #Hall⟩
  iapply wp (keyOrder isItem h) t (zs.map (entry h)) $$ [Ht]
  · iframe # ∗
  inext
  iintro %t2 ⟨Ht, Ht2⟩
  iapply HΦ
  isplitl [Ht]
  · iexists h, zs; iframe # ∗; ipureintro; exact Hzs
  · iexists h, zs; iframe # ∗; ipureintro; exact Hzs

open Classical in
theorem btree.BTree.AscendGreaterOrEqual.modelSpec_of (wp : btree.BTree.AscendGreaterOrEqual.spec (GF := GF) (hG := hG)) :
    btree.BTree.AscendGreaterOrEqual.modelSpec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V t isItem _ less _ items dq pivot vp iter P Q
  wp_start_folded as ⟨%Hswo, Ht, #Hp, HP, #Hit⟩
  unfold EtcdGrove.ownBTree
  icases Ht with ⟨%h, %zs, Ht, %Hzs, #Hall⟩
  subst Hzs
  ihave #Hproto := iterProtocol_of_btIterSpec isItem h zs
    (zs.filter (fun z => !decide (less z.2 vp))) (fun z hz => (List.mem_filter.1 hz).1) iter P Q
    _ (btAscendGe_entries zs vp)
    (btree.ascRange (keyOrder isItem h).lt (zs.map (entry h)) (some (EtcdGrove.key h vp)) none)
    (ascRange_ge_entries zs vp) $$ [Hall Hit]
  · iframe #
  iapply wp (keyOrder isItem h) t dq (zs.map (entry h)) pivot (EtcdGrove.key h vp) iter
    (fun pre b => if b then Q else P pre.length) $$ [Ht HP]
  · iframe # ∗
    isplitr
    · iapply keyOrder_item; iexact Hp
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil]; iexact HP
  inext
  iintro ⟨Ht, Hdone⟩
  iapply HΦ
  isplitl [Ht]
  · iexists h, zs; iframe # ∗; ipureintro; rfl
  · iapply iterDone_model _ P Q _ _ $$ Hdone
    show _ = (btree.ascRange (keyLt h) (zs.map (entry h)) (some (EtcdGrove.key h vp)) none).length
    rw [btAscendGe_entries, ascRange_ge_entries]; simp

open Classical in
theorem btree.BTree.AscendRange.modelSpec_of (wp : btree.BTree.AscendRange.spec (GF := GF) (hG := hG)) :
    btree.BTree.AscendRange.modelSpec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V t isItem _ less _ items dq ge lt vge vlt iter P Q
  wp_start_folded as ⟨%Hswo, Ht, #Hge, #Hlt, HP, #Hit⟩
  unfold EtcdGrove.ownBTree
  icases Ht with ⟨%h, %zs, Ht, %Hzs, #Hall⟩
  subst Hzs
  ihave #Hproto := iterProtocol_of_btIterSpec isItem h zs
    (zs.filter (fun z => !decide (less z.2 vge) && decide (less z.2 vlt)))
    (fun z hz => (List.mem_filter.1 hz).1) iter P Q
    _ (btAscendRange_entries zs vge vlt)
    (btree.ascRange (keyOrder isItem h).lt (zs.map (entry h)) (some (EtcdGrove.key h vge))
      (some (EtcdGrove.key h vlt)))
    (ascRange_range_entries zs vge vlt) $$ [Hall Hit]
  · iframe #
  iapply wp (keyOrder isItem h) t dq (zs.map (entry h)) ge (EtcdGrove.key h vge) lt
    (EtcdGrove.key h vlt) iter (fun pre b => if b then Q else P pre.length) $$ [Ht HP]
  · iframe # ∗
    isplitr
    · iapply keyOrder_item; iexact Hge
    isplitr
    · iapply keyOrder_item; iexact Hlt
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil]; iexact HP
  inext
  iintro ⟨Ht, Hdone⟩
  iapply HΦ
  isplitl [Ht]
  · iexists h, zs; iframe # ∗; ipureintro; rfl
  · iapply iterDone_model _ P Q _ _ $$ Hdone
    show _ = (btree.ascRange (keyLt h) (zs.map (entry h)) (some (EtcdGrove.key h vge))
      (some (EtcdGrove.key h vlt))).length
    rw [btAscendRange_entries, ascRange_range_entries]; simp

end model

end EtcdGrove
end Perennial
