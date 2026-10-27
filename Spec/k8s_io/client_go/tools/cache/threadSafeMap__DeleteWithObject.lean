/-
`(*threadSafeMap).DeleteWithObject(key, obj)` (`thread_safe_store.go:336`): removes the key, and
takes the object's resource version, under the write lock. Lean-first.
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

/-- **`c.DeleteWithObject(key, obj)`**, logically atomic, for `obj` `nil` or meeting `OK` (with
the accessor's contract if not `nil`): the key is not in the items, and the resource version
becomes the object's if it is not `nil` and its accessor has one (`rvOfObj`). -/
abbrev threadSafeMap.DeleteWithObject.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (rvOf : GoInterface → Option GoString) (key : GoString) (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      okNil OK obj ∗ □ (⌜obj ≠ interface.nil⌝ -∗ rvAcc OK rvOf) }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"DeleteWithObject"))
      (Val #key)) (Val #obj))
    @@ ∅
  <<{ storeSt γ (σ.delete key (rvOfObj rvOf obj)) }>>
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
