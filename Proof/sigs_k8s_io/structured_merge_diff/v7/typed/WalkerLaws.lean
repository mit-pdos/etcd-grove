/-
**The laws of the `typed` walkers' vocabulary** (`Walkers.lean`): stated, not proved (Draft,
2026-11-19): each a `def <name>.law : Prop`, proved after the freeze by `<name>_law_holds`. They
are the invariant work of the next phase: what the walkers' proofs and the `TypedValue` glue use.

- the package fact: `typedPkgInit_pools` (true once `Base.lean`'s fact is `typedPools`);
- representation: `isTV_isTVv`, persistence, `ownCmp_persist` (a finished comparison handed out),
  the zero walkers pooled (`*_zero_pooled`: a pool's `New`), `spareWalkers_nil`, `ownPath_nil`;
- the pure operations at a node (what makes a walker's step the abstract function's): fuel
  (`mergeF_fuel`, `cmpF_fuel`), the branch equations (`mergeO_leaf`, `mergeO_list`,
  `mergeO_map`, `cmpO_below`), presence (`mergeO_some`), conformance (`merge_conforms`, and the
  children's: `conforms_item`, `conforms_entry`), the set sizes (`fieldSet_card`, `cmpO_card`),
  `removeAt_scalar`, the reconcile walker's result (`reconOut_reconcile`, `reconOut_scalar`,
  `reconOut_granular`);
- the API's readings: `merge_mergeO`, `compare_cmpO`, `fieldSet_fieldsAt`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Pure laws -/

/-- `Merge`'s result is the walker's at the root. -/
def merge_mergeO.law : Prop :=
  ∀ S t l r, merge S t l r = (mergeO S t (some l) (some r)).getD .null

/-- `Compare`'s result is the walker's at the root. -/
def compare_cmpO.law : Prop := ∀ S t l r, compare S t l r = cmpO S t [] (some l) (some r)

/-- `ToFieldSet`'s result is the walker's at the root. -/
def fieldSet_fieldsAt.law : Prop := ∀ S t x, fieldSet S t x = fieldsAt S t [] x

/-- More fuel changes nothing. -/
def mergeF_fuel.law : Prop :=
  ∀ n S t l r, fuelO l r ≤ n → mergeF n S t l r = mergeO S t l r
def cmpF_fuel.law : Prop :=
  ∀ n S t p l r, fuelO l r ≤ n → cmpF n S t p l r = cmpO S t p l r

/-- At a leaf the merge is the right side, else the left (`doLeaf`'s rule). -/
def mergeO_leaf.law : Prop :=
  ∀ S t l r, leafAt S t l r = true → (l.isSome ∨ r.isSome) → mergeO S t l r = leafM l r

/-- A granular list's merge is its items' (`visitListItems`). -/
def mergeO_list.law : Prop :=
  ∀ S t e rel ks l r, S.find t.name = some (.list e rel ks) → leafAt S t l r = false →
    mergeO S t l r = mergeListOut (fuelL (listItems l) (listItems r)) S e ks (listItems l) (listItems r)

/-- A granular map's merge is its entries' (`visitMapItems`). -/
def mergeO_map.law : Prop :=
  ∀ S t fs e rel l r, S.find t.name = some (.map fs e rel) → leafAt S t l r = false →
    mergeO S t l r = mergeMapOut (fuelM (mapItems l) (mapItems r)) S fs e (mapItems l) (mapItems r)

/-- `compare` adds the node itself after `doList`/`doMap` when the node is not a leaf. -/
def cmpO_below.law : Prop :=
  ∀ S t p l r, cmpO S t p l r =
    if leafAt S t l r then cmpBelow S t p l r else (cmpBelow S t p l r).union (nodeC p l r)

/-- The merge of conforming sides, one present, is present (the top `merge` never returns a nil
value in the scope). -/
def mergeO_some.law : Prop :=
  ∀ S t l r, S.WF → confO S t l → confO S t r → (l.isSome ∨ r.isSome) →
    (mergeO S t l r).isSome

/-- The merge of conforming values conforms (`Merge`'s `isTV`; Go: every result of the random
sequences validates). -/
def merge_conforms.law : Prop :=
  ∀ S t l r, S.WF → conforms S t l → conforms S t r → conforms S t (merge S t l r)

/-- A conforming list's items conform to the element type, are keyed, keys distinct. -/
def conforms_item.law : Prop :=
  ∀ S t e rel ks vs, S.find t.name = some (.list e rel ks) → conforms S t (.list vs) →
    (∀ v ∈ vs, conforms S e v) ∧
    (rel = .associative → (∀ v ∈ vs, itemKeyOk ks v) ∧ (keysOf ks vs).Nodup)

/-- A conforming map's entries conform to their types. -/
def conforms_entry.law : Prop :=
  ∀ S t fs e rel kvs, S.find t.name = some (.map fs e rel) → conforms S t (.map kvs) →
    ∀ k v, (k, v) ∈ kvs → ∃ t', fieldType fs e k = some t' ∧ conforms S t' v

/-- The field set of a value has at most as many paths as the value has nodes (each path is a
node): the walkers' size premise from the API's. -/
def fieldSet_card.law : Prop :=
  ∀ S t p x, x.size < typedSizeMax → (fieldsAt S t p x).CardLt typedSizeMax
def cmpO_card.law : Prop :=
  ∀ S t p l r, sizeO l + sizeO r < typedSizeMax →
    (cmpO S t p l r).removed.CardLt typedSizeMax ∧ (cmpO S t p l r).modified.CardLt typedSizeMax ∧
    (cmpO S t p l r).added.CardLt typedSizeMax

/-- At a scalar type `removeAt` is the identity (`removingWalker.doScalar`). -/
def removeAt_scalar.law : Prop :=
  ∀ S t s R x, S.find t.name = some (.scalar s) → removeAt S t R x = x

/-- The reconcile walker's result at the root is `reconcile` (`ReconcileFieldSetWithSchema`):
`toRemove` and `toAdd` both `reconOut S t [] false s`, the result `s` less every path with a
prefix in it, plus it; and `nil` (`none`) means nothing to change. -/
def reconOut_reconcile.law : Prop :=
  ∀ S t s, S.WF →
    match reconOut S t [] false s with
    | none => reconcile S t s = s
    | some N => reconcile S t s = (s.filter (fun q => !N.any (fun p => p.isPrefixOf q))).union N

/-- A scalar node adds nothing. -/
def reconOut_scalar.law : Prop :=
  ∀ S t p b F s, S.find t.name = some (.scalar s) → reconOut S t p b F = none

/-- A granular node, or one reached as a member without children, adds the atomic nodes below. -/
def reconOut_granular.law : Prop :=
  ∀ S t p b F, reconTouch S t b F = false → reconOut S t p b F = reconBelow S t p F

/-- `optU` is associative, commutative, idempotent (the walkers' accumulators). -/
def optU_assoc.law : Prop := ∀ a b c, optU (optU a b) c = optU a (optU b c)
def optU_idem.law : Prop := ∀ a b, optU a (optU a b) = optU a b

/-! ## Representation laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The package fact** (true once `Base.lean`'s `isPkgInit typed` is `typedPools`, proved by
the generated initializer: `etc/gen-init.py`'s `SPECIAL`). -/
def typedPkgInit_pools.law : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ⊢ typedPools (GF := GF)

/-- A typed value at `p` is a persistent pointer to a `TypedValue` struct holding it. -/
def isTV_isTVv.law : Prop :=
  ∀ p sc S t x, isTV (GF := GF) p sc S t x ⊣⊢ ∃ tv, p ↦□ tv ∗ isTVv tv sc S t x

/-- A validated value: `isTVu` at the discarded fraction with conformance is `isTVv`. -/
def isTVu_isTVv.law : Prop :=
  ∀ tv sc S t x, isTVu (GF := GF) tv sc S t x DFrac.discard ∗ ⌜conforms S t x⌝ ⊣⊢ isTVv tv sc S t x

def isTVv_persistent.law : Prop :=
  ∀ tv sc S t x, isTVv (GF := GF) tv sc S t x ⊢ □ isTVv tv sc S t x
def isComparison_persistent.law : Prop :=
  ∀ c C, isComparison (GF := GF) c C ⊢ □ isComparison c C

/-- What a client reads of a comparison (its three fields and sets). -/
def isComparison_open.law : Prop :=
  ∀ c C, isComparison (GF := GF) c C ⊣⊢ ∃ (r m a : Loc), c ↦□ (typed.Comparison.mk r m a) ∗
    isSet r C.removed ∗ isSet m C.modified ∗ isSet a C.added

/-- A finished comparison is handed out (`Compare`'s return). -/
def ownCmp_persist.law : Prop := ∀ c C, ownCmp (GF := GF) c C ⊢ |==> isComparison c C

/-- A side lent at a fraction is persistent at the discarded one. -/
def isValO_persist.law : Prop := ∀ v dq o, isValO (GF := GF) v dq o ⊢ |==> isValO v DFrac.discard o

def outRep_persistent.law : Prop := ∀ o x, outRep (GF := GF) o x ⊢ □ outRep o x

/-- Before the first descent. -/
def spareWalkers_nil.law : Prop :=
  ∀ (V : Type) [TypedPointsto (GF := GF) V], ⊢ spareWalkers (GF := GF) V null
def ownPath_nil.law : Prop := ⊢ ownPath (GF := GF) slice.nil []

/-- A pool's `New` makes a pooled walker (the zero struct). -/
def mw_zero_pooled.law : Prop :=
  ∀ w, w ↦ (zero_val typed.mergingWalker) ⊢ mwPooled (GF := GF) w
def cw_zero_pooled.law : Prop :=
  ∀ w, w ↦ (zero_val typed.compareWalker) ⊢ cwPooled (GF := GF) w
def tw_zero_pooled.law : Prop :=
  ∀ w, w ↦ (zero_val typed.toFieldSetWalker) ⊢ twPooled (GF := GF) w
def vw_zero_pooled.law : Prop :=
  ∀ w, w ↦ (zero_val typed.validatingObjectWalker) ⊢ vwPooled (GF := GF) w
def rw_zero_pooled.law : Prop :=
  ∀ w, w ↦ (zero_val typed.reconcileWithSchemaWalker) ⊢ rwPooled (GF := GF) w

end laws

end smd
end EtcdGrove
end Perennial
