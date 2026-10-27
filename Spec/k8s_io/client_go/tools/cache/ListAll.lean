/-
`ListAll(store, selector, appendFn)` (`listers.go:34`): `appendFn` on each of the store's items
the selector matches. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.ListerDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- An `AppendFunc`'s contract: from `A ms`, on an object meeting `OK`, `A (ms ++ [m])`. -/
def appendOk (OK : GoInterface → IProp GF) (af : GoFunc) (A : List GoInterface → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (ms : List GoInterface) (m : GoInterface),
    {{ A ms ∗ □ OK m }} (App (Val #af) (Val #m)) {{ RET #(); A (ms ++ [m]) }})

instance appendOk_persistent (OK : GoInterface → IProp GF) (af : GoFunc)
    (A : List GoInterface → IProp GF) : Persistent (appendOk OK af A) := by
  unfold appendOk; infer_instance

/-- **`ListAll(ca, sel, af)`**, logically atomic (a reader), for the cache `ca` (as a `Store`), a
selector that selects everything and a store without `nil` items: `af` on each item of the store
at the linearization point (its `List()`), each once, in some order. -/
abbrev ListAll.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn) (kf : GoFunc)
    (sel : GoInterface) (af : GoFunc) (A : List GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ everySel sel ∗ appendOk OK af A ∗ A [] }}
  <<{ ∀∀ σ, storeSt γ σ ∗ ⌜noNil σ.items⌝ }>>
    (App (App (App (Val (@! ListAll))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca)))
      (Val #sel)) (Val #af))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items⌝ }>>
  {{ RET #interface.nil; ∃ ks : List GoString,
      ⌜ks.Nodup ∧ ∀ k, k ∈ ks ↔ k ∈ σ.items⌝ ∗ A (ks.map (objAt σ.items)) ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
