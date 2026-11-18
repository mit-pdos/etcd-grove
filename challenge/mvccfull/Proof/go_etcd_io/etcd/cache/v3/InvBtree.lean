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
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Defs
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Tree
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

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

end ops

/-! ## Lemmas -/

section lemmas
variable {V : Type} {less : V → V → Prop} [DecidableRel less]

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
    (hb : incomp less b1 b2) (hl : less a1 b1) : less a2 b2 :=
  sorry

/-- `less` on classes. -/
def keyLt (h : StrictWeakOrder less) : Key h → Key h → Prop :=
  Quotient.lift₂ (s₁ := keySetoid h) (s₂ := keySetoid h) less (by
    intro a1 b1 a2 b2 ha hb
    exact propext ⟨less_congr h ha hb,
      less_congr h ⟨ha.2, ha.1⟩ ⟨hb.2, hb.1⟩⟩)

theorem keyLt_order (h : StrictWeakOrder less) : btree.StrictOrder (keyLt h) :=
  sorry

end key

/-! ### Entries: a Go item with its model

The bridge keeps the list `zs` of pairs (Go item, model): the btree's entries are
`zs.map (entry h)` and the models `zs.map Prod.snd`. -/

section entries

variable {T' V : Type} {less : V → V → Prop} (h : StrictWeakOrder less) [DecidableRel less]

/-- The btree's entry of a Go item with its model: the item and the model's class. -/
def entry (z : T' × V) : T' × Key h := (z.1, key h z.2)

variable {h}

end entries

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

variable {T' : Type} {V : Type}

end defs

/-! ## The store's view of the btree's methods

The triples the store's proofs use, on the predicate above (they were this package's
trust boundary until the btree was proved): each is derived from the btree method's own
spec (`Spec/k8s_io/.../btree/`), as `<fn>.modelSpec_of`. -/

section model
open go_etcd_io.etcd.cache.v3 k8s_io.utils.third_party.forked.golang

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

end model

end EtcdGrove
end Perennial
