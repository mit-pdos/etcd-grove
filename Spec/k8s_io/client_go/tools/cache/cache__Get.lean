/-
`(*cache).Get(obj)` (`store.go`): the key function's key, then `GetByKey`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the `cache` wrapper, `store.go`).
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

/-- **`c.Get(obj)`**, logically atomic (a reader): the item at the object's key (`KF obj`;
the key function's contract is the call's, `keyOk D kf KF` with `D` covering `obj`). -/
abbrev cache.Get.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (D : GoInterface → IProp GF) (KF : GoInterface → GoString)
    (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗ keyOk D kf KF ∗ □ D obj ∗
      tsReader ts γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"Get")) (Val #obj))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (item : GoInterface) (ok : Bool), RET (PairV (PairV #item #ok) #interface.nil);
      ⌜item = objAt σ.items (KF obj) ∧ ok = decide (KF obj ∈ σ.items)⌝ ∗ okNil OK item ∗
      tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
