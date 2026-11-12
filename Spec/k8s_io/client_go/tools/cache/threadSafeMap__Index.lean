/-
`(*threadSafeMap).Index(indexName, obj)` (`thread_safe_store.go:422`): the items whose indexed
values under the indexer include one of the values the indexer gives `obj`, under the read lock.
Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the namespace listers' path,
`ListAllByNamespace`).
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

/-- What `Index(n, obj)` returns, at the linearization point's state `σ`: for an indexer `n` (its
relation `F`), no error, `obj`'s values `vq` under it (`F obj vq`) and a new slice of the items
whose values under it share one with `vq` (`idxSel`: exactly those, each once, in some order),
each with its contract; otherwise an error. -/
def indexPost (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (σ : St) (n : GoString)
    (obj : GoInterface) (sl : GoSlice) (err : GoInterface) : IProp GF :=
  match (σ.fns Fam) !! n with
  | none => iprop(⌜err ≠ interface.nil⌝)
  | some F => iprop(⌜err = interface.nil⌝ ∗ ∃ (vq ks : List GoString),
      ⌜ks.Nodup⌝ ∗ □ F obj vq ∗ idxSel F σ.items (fun vs => ∃ v ∈ vq, v ∈ vs) ks ∗
      sl ↦* (ks.map (objAt σ.items)) ∗ ([∗list] o ∈ ks.map (objAt σ.items), okNil OK o))

/-- **`c.Index(n, obj)`**, logically atomic (`indexPost`), for `obj` meeting the index functions'
contract (`OK`: the listers' query objects are the client's to cover). Needs one of the lock's
reader slots. -/
abbrev threadSafeMap.Index.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (n : GoString)
    (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      tsReader c γ OK Fam ∗ □ OK obj }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"Index")) (Val #n))
      (Val #obj))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      indexPost OK Fam σ n obj sl err ∗ tsReader c γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
