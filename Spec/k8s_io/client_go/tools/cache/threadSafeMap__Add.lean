/-
`(*threadSafeMap).Add(key, obj)` (`thread_safe_store.go:308`): `Update(key, obj)`. Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.Add(key, obj)`**: `Update`'s spec. -/
abbrev threadSafeMap.Add.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (rvOf : GoInterface → Option GoString) (key : GoString) (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      rvAcc OK rvOf ∗ □ OK obj }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"Add")) (Val #key))
      (Val #obj))
    @@ ∅
  <<{ storeSt γ (σ.update key obj (rvOf obj)) }>>
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
