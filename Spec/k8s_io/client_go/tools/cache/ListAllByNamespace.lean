/-
`ListAllByNamespace(indexer, namespace, selector, appendFn)` (`listers.go:61`): `appendFn` on each
of the namespace's items (through the namespace index), or each item for `NamespaceAll` (`""`).
Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.ListAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- The namespace index's query object at `q`. -/
def qObj [FfiSyntax] [GoGlobalContext] (q : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty) #q

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The store's contract covers the namespace index's query objects of namespace `ns` (the client's
to give: the index functions run on them). -/
def qOk (OK : GoInterface → IProp GF) (ns : GoString) : IProp GF :=
  iprop(□ ∀ q : Loc, q ↦□ qMeta ns -∗ □ OK (qObj q))

instance qOk_persistent (OK : GoInterface → IProp GF) (ns : GoString) :
    Persistent (qOk OK ns) := by
  unfold qOk; infer_instance

/-- The keys a `ListAllByNamespace(…, ns, …)` visits at the store's state `σ`: every key for
`ns = ""`; otherwise those the namespace index (`F`, the store's `"namespace"` indexer) has under
the query object's values. -/
def nsKeys (F : Fn) (σ : St) (ns : GoString) (q : Loc) (ks : List GoString) :
    Prop :=
  ks.Nodup ∧ if ns = [] then ∀ k, k ∈ ks ↔ k ∈ σ.items
    else ∀ k, k ∈ ks ↔ ∃ v ∈ F (qObj q), inIdx F σ.items v k

/-- **`ListAllByNamespace(ca, ns, sel, af)`**, logically atomic (a reader), for the cache `ca` (as
an `Indexer`), a selector that selects everything, a store without `nil` items and, for a
namespace, the namespace indexer `F` (so the slow path without an index is not taken): `af` on
each item of the namespace (`nsKeys`) at the linearization point, each once, in some order. -/
abbrev ListAllByNamespace.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn) (kf : GoFunc)
    (ns : GoString) (sel : GoInterface) (af : GoFunc) (A : List GoInterface → IProp GF) (F : Fn),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ everySel sel ∗ appendOk OK af A ∗ A [] ∗ qOk OK ns }}
  <<{ ∀∀ σ, storeSt γ σ ∗
      ⌜noNil σ.items ∧ (ns ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
    (App (App (App (App (Val (@! ListAllByNamespace))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca)))
      (Val #ns)) (Val #sel)) (Val #af))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items ∧ (ns ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
  {{ RET #interface.nil; ∃ (q : Loc) (ks : List GoString),
      ⌜nsKeys F σ ns q ks⌝ ∗ (if ns = [] then iprop(True) else q ↦□ qMeta ns) ∗
      A (ks.map (objAt σ.items)) ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
