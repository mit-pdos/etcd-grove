/-
`(*cache).GetByKey(key)` (`store.go`): the thread-safe store's `Get`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the `cache` wrapper, `store.go`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs

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

/-- **`c.GetByKey(key)`**, logically atomic (a reader): the key's item (`nil`, `false` if
none). Needs one of the store lock's reader slots. -/
abbrev cache.GetByKey.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗ tsReader ts γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"GetByKey")) (Val #key))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (item : GoInterface) (ok : Bool), RET (PairV (PairV #item #ok) #interface.nil);
      ⌜item = objAt σ.items key ∧ ok = decide (key ∈ σ.items)⌝ ∗ okNil OK item ∗
      tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
