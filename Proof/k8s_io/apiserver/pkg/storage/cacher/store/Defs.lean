/-
**The watch cache's store, as the specs see it** (KEP-6404, `notes/kep-6404-plan.md`;
2026-10-26). Lean-first (no Rocq counterpart).

`k8s.io/apiserver/pkg/storage/cacher/store` keeps the watch cache's objects in a B-tree of
`*Element`s ordered by their keys (`btreeStore`, over the verified fork of google/btree,
`Proof/k8s_io/utils/third_party/forked/golang/btree/`), and after every write publishes an
immutable clone of it (`latestSnapshot`), which readers use without a lock.

* `elemOrder`: the B-tree's order on elements, Go's order on their keys (`GoStringLt`); an element
  is related to the key its `Key` field holds, read-only (the store never writes an element; the
  watch cache builds each one before handing it over).
* `ownStore p dq s rv`: the `btreeStore` at `p` (its two fields, `tree` and `resourceVersion`) holds the entries `s` (elements
  with their keys, strictly increasing) at the resource version `rv`, at fraction `dq`.
* `isSnap p s rv`: the same, read-only for good (`DFrac.discard`, persistent): a published
  snapshot, which no one writes again (every write to the store goes to the store's own tree,
  of which a snapshot is a `Clone`).
-/
module

public import GeneratedProof.k8s_io.apiserver.pkg.storage.cacher.store
public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Defs
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Fractional
public import Perennial.Golang.Theory.String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher.store

/-- Go's order on strings is a strict total order (the B-tree's `StrictOrder`). -/
theorem goStringLt_strictOrder : btree.StrictOrder go.GoStringLt where
  irrefl := go.goStringLt_irrefl
  trans _ _ _ h1 h2 := go.goStringLt_trans h1 h2
  total a b := by
    by_cases h1 : go.GoStringLt a b
    · exact Or.inl h1
    · by_cases h2 : go.GoStringLt b a
      · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl (go.goStringLt_eq_of_not_lt h1 h2))

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- **The store's order on elements** (see the file header). -/
def elemOrder : btree.ItemOrder GF Loc GoString where
  lt := go.GoStringLt
  order := goStringLt_strictOrder
  item e k := iprop(structFieldRef k8s_io.apiserver.pkg.storage.cacher.store.Element go!"Key" e ↦□ k)
  item_persistent _ _ := by infer_instance

/-- **A `btreeStore` holding the entries `s` at resource version `rv`** (see the file header). -/
def ownStore (p : Loc) (dq : DFrac) (s : List (Loc × GoString)) (rv : w64) : IProp GF :=
  iprop(∃ t : Loc, structFieldRef k8s_io.apiserver.pkg.storage.cacher.store.btreeStore go!"tree" p ↦{dq} t ∗
    structFieldRef k8s_io.apiserver.pkg.storage.cacher.store.btreeStore go!"resourceVersion" p ↦{dq} rv ∗
    btree.ownBTree elemOrder t dq s)

/-- **A published snapshot** (persistent; see the file header). -/
def isSnap (p : Loc) (s : List (Loc × GoString)) (rv : w64) : IProp GF :=
  ownStore p DFrac.discard s rv

instance isSnap_persistent (p : Loc) (s : List (Loc × GoString)) (rv : w64) :
    Persistent (isSnap (GF := GF) p s rv) := by
  unfold isSnap ownStore; infer_instance

/-- The element (if any) with key `k` in the entries `s`, as `getByKey` returns it: the B-tree's
`Get` gives the zero `*Element` (`nil`) when there is none. -/
def lookupElem (s : List (Loc × GoString)) (k : GoString) : Loc :=
  (btree.lookup s k).getD (zero_val Loc)

end defs

end cacher
end EtcdGrove
end Perennial
