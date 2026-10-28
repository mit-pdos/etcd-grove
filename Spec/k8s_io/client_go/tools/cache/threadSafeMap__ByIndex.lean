/-
`(*threadSafeMap).ByIndex(indexName, indexedValue)` (`thread_safe_store.go:478`): the items whose
indexed values under the indexer include the value, under the read lock. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- What `ByIndex(n, v)` returns, at the linearization point's state `σ`: for an indexer `n` (its
relation `F`), no error and a new slice of the items whose objects' values under it contain `v`
(`idxSel`: exactly those, each once, in some order, with the relation holding of each item's
values), each with its contract; otherwise an error. -/
def byIndexPost (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (σ : St) (n v : GoString)
    (sl : GoSlice) (err : GoInterface) : IProp GF :=
  match (σ.fns Fam) !! n with
  | none => iprop(⌜err ≠ interface.nil⌝)
  | some F => iprop(⌜err = interface.nil⌝ ∗ ∃ ks : List GoString,
      ⌜ks.Nodup⌝ ∗ idxSel F σ.items (fun vs => v ∈ vs) ks ∗ sl ↦* (ks.map (objAt σ.items)) ∗
      ([∗list] o ∈ ks.map (objAt σ.items), okNil OK o))

/-- **`c.ByIndex(n, v)`**, logically atomic (`byIndexPost`). Needs one of the lock's reader
slots. -/
abbrev threadSafeMap.ByIndex.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (n v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      tsReader c γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"ByIndex")) (Val #n))
      (Val #v))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      byIndexPost OK Fam σ n v sl err ∗ tsReader c γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
