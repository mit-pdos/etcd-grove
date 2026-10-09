/-
The btree `k8s.io/utils/third_party/forked/golang/btree` (a fork of `google/btree`) as the
trust boundary of etcd's `cache` store: the package is translated names-only
(`Code/k8s_io/.../btree.toml`), so its methods are axioms here
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
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Spec.k8s_io.utils.third_party.forked.golang.btree.New
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__ReplaceOrInsert
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Get
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Delete
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Clone
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__AscendGreaterOrEqual
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__AscendRange

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
relates each entry of the btree to its model by `isItem`. -/

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

/-- `less` on classes. -/
def keyLt (h : StrictWeakOrder less) : Key h → Key h → Prop :=
  Quotient.lift₂ (s₁ := keySetoid h) (s₂ := keySetoid h) less (by
    sorry)

theorem keyLt_key (h : StrictWeakOrder less) (a b : V) :
    keyLt h (key h a) (key h b) ↔ less a b := Iff.rfl

theorem keyLt_order (h : StrictWeakOrder less) : btree.StrictOrder (keyLt h) := by
  sorry

end key

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
shared for good). The btree's own `btree.ownBTree` on the classes of the models. -/
def ownBTree {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) (items : List V) (dq : DFrac) : IProp GF :=
  iprop(∃ (h : StrictWeakOrder less) (s : List (T' × Key h)),
    btree.ownBTree (keyOrder isItem h) t dq s ∗
    ⌜s.map Prod.snd = items.map (key h)⌝ ∗
    [∗list] e;v ∈ s;items, isItem e.1 v)

instance ownBTree_persistent {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) (items : List V) :
    Persistent (ownBTree T t isItem less items DFrac.discard) := by
  sorry

/-- Make an owned tree read-only for good (`ownBTree … dq ==∗ ownBTree … discard`). -/
theorem ownBTree_persist {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) (items : List V) (dq : DFrac) :
    ownBTree T t isItem less items dq ⊢ |==> ownBTree T t isItem less items DFrac.discard := by
  sorry

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

theorem btree.New.modelSpec_of (wp : btree.New.spec (GF := GF) (hG := hG)) :
    btree.New.modelSpec (GF := GF) (hG := hG) := by
  sorry

theorem btree.BTree.ReplaceOrInsert.modelSpec_of (wp : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG)) :
    btree.BTree.ReplaceOrInsert.modelSpec (GF := GF) (hG := hG) := by
  sorry

theorem btree.BTree.Get.modelSpec_of (wp : btree.BTree.Get.spec (GF := GF) (hG := hG)) :
    btree.BTree.Get.modelSpec (GF := GF) (hG := hG) := by
  sorry

theorem btree.BTree.Delete.modelSpec_of (wp : btree.BTree.Delete.spec (GF := GF) (hG := hG)) :
    btree.BTree.Delete.modelSpec (GF := GF) (hG := hG) := by
  sorry

theorem btree.BTree.Clone.modelSpec_of (wp : btree.BTree.Clone.spec (GF := GF) (hG := hG)) :
    btree.BTree.Clone.modelSpec (GF := GF) (hG := hG) := by
  sorry

theorem btree.BTree.AscendGreaterOrEqual.modelSpec_of (wp : btree.BTree.AscendGreaterOrEqual.spec (GF := GF) (hG := hG)) :
    btree.BTree.AscendGreaterOrEqual.modelSpec (GF := GF) (hG := hG) := by
  sorry

theorem btree.BTree.AscendRange.modelSpec_of (wp : btree.BTree.AscendRange.spec (GF := GF) (hG := hG)) :
    btree.BTree.AscendRange.modelSpec (GF := GF) (hG := hG) := by
  sorry

end model

end EtcdGrove
end Perennial
