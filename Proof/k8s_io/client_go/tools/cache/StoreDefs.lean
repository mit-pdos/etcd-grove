/-
The ownership predicates of client-go's thread-safe store (`tools/cache/thread_safe_store.go`),
over its pure model (`StoreModel.lean`). Lean-first.

* `ownIxN l dq X`: one indexer's index, the map `l` from values to sets, each set owned.
-/
module

public import Proof.k8s_io.client_go.tools.cache.StoreModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- One indexer's index at `l`: the map of values to the sets' locations, and each set's keys. -/
def ownIxN (l : Loc) (dq : DFrac) (X : IxN) : IProp GF :=
  iprop(l ↦${dq} (GMap.fmap Prod.fst X) ∗ [∗map] _v ↦ e ∈ X, e.1 ↦${dq} e.2)

/-- The indices at `ip`: the map of indexers' names to their indices, each index owned. -/
def ownIx (ip : Loc) (dq : DFrac) (ix : Ix) : IProp GF :=
  iprop(ip ↦${dq} (GMap.fmap Prod.fst ix) ∗ [∗map] _n ↦ e ∈ ix, ownIxN e.1 dq e.2)

/-- An object the store may hold: `nil`, or one meeting the client's contract `OK`. -/
def okNil (OK : GoInterface → IProp GF) (o : GoInterface) : IProp GF :=
  iprop(⌜o = interface.nil⌝ ∨ □ OK o)

instance okNil_persistent (OK : GoInterface → IProp GF) (o : GoInterface) :
    Persistent (okNil OK o) := by
  unfold okNil; infer_instance

/-- **An index function's contract**: `f` is not `nil`, and on an object meeting `OK` it returns
no error and the values `F o` (in a slice the caller may read). -/
def fnOk (OK : GoInterface → IProp GF) (f : GoFunc) (F : Fn) : IProp GF :=
  iprop(⌜f ≠ func.nil⌝ ∗ ∀ o : GoInterface, {{ □ OK o }} (App (Val #f) (Val #o))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
        ⌜err = interface.nil⌝ ∗ ∃ dq, sl ↦*{dq} F o }})

instance fnOk_persistent (OK : GoInterface → IProp GF) (f : GoFunc) (F : Fn) :
    Persistent (fnOk OK f F) := by
  unfold fnOk; infer_instance

/-- **The indexers' contracts**: the indexers' map `fv` has the indexers of `fns`, each function
meeting its contract. -/
def fnsOk (OK : GoInterface → IProp GF) (fv : GMap GoString GoFunc) (fns : GMap GoString Fn) :
    IProp GF :=
  iprop(⌜∀ n, n ∈ fns ↔ n ∈ fv⌝ ∗ [∗map] n ↦ f ∈ fv, ∃ F, ⌜fns !! n = some F⌝ ∗ fnOk OK f F)

instance fnsOk_persistent (OK : GoInterface → IProp GF) (fv : GMap GoString GoFunc)
    (fns : GMap GoString Fn) : Persistent (fnsOk OK fv fns) := by
  unfold fnsOk; infer_instance

/-- The indexers' map in two halves. -/
theorem fvMap_halves (l : Loc) (fv : GMap GoString GoFunc) (q : Qp) :
    (l ↦${DFrac.own q} fv : IProp GF) ⊣⊢ l ↦${DFrac.own q.half} fv ∗ l ↦${DFrac.own q.half} fv := by
  conv => lhs; rw [← Qp.half_add_half q]
  exact (ownMap_fractional (GF := GF) l fv).fractional _ _

end defs

end cache
end EtcdGrove
end Perennial
