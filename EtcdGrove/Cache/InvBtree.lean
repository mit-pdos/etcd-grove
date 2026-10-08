/-
The btree `k8s.io/utils/third_party/forked/golang/btree` (a fork of `google/btree`) as the
trust boundary of etcd's `cache` store: the package is translated names-only
(`EtcdCache/Code/k8s_io/.../btree.toml`), so its methods are axioms here
(`Spec/btree_New.lean`, `Spec/BTree__*.lean`, each with an `axiom … .wp_proof`), stated
over the **axiomatized** predicate `ownBTree` below. Lean-first (no Rocq counterpart).

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
import EtcdGrove.Cache.Base

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

/-! ## The axiomatized predicate -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary.** `ownBTree T t isItem less items dq`: `t` is a `*btree.BTree[T]`
(Lean representation `T'` of the Go type `T`) holding, in order, Go items modelling
`items` (by `isItem`), with the `LessFunc` it was created with deciding `less`; owned
with fraction `dq` (`DFrac.own 1` to write, any fraction to read, `DFrac.discard` for a
read-only tree shared for good). An axiom: the btree package is translated names-only,
so there is no definition to unfold. -/
axiom ownBTree {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) (less : V → V → Prop) (items : List V)
    (dq : DFrac) : IProp GF

/-- **Trust boundary.** `ownBTree` is fractional in `dq` (`dq₁ • dq₂` splits into `dq₁`
and `dq₂`, which is how `typedPointsto` is), with `DFrac.discard` persistent and any
fraction persistable (`dq ==∗ discard`): Perennial's `DFractional`, as for
`typedPointsto`. In the btree's model it is a predicate on read-only-shareable heap
cells (the nodes, the `BTree` struct, the copy-on-write context). -/
axiom ownBTree_dfractional {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) (less : V → V → Prop) (items : List V) :
    DFractional (ownBTree T t isItem less items)

attribute [instance] ownBTree_dfractional

instance ownBTree_persistent {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) (less : V → V → Prop) (items : List V) :
    Persistent (ownBTree T t isItem less items DFrac.discard) :=
  (ownBTree_dfractional T t isItem less items).dfractional_persistent

/-- Make an owned tree read-only for good (`ownBTree … dq ==∗ ownBTree … discard`). -/
theorem ownBTree_persist {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) (less : V → V → Prop) (items : List V)
    (dq : DFrac) :
    ownBTree T t isItem less items dq ⊢ |==> ownBTree T t isItem less items DFrac.discard :=
  (ownBTree_dfractional T t isItem less items).dfractional_persist dq

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

end defs

end EtcdGrove
end Perennial
