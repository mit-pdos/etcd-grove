/-
`(*threadSafeMap).Update(key, obj)` (`thread_safe_store.go:312`): stores the object, indexes it,
and takes its resource version, under the write lock. Lean-first.
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

/-- **`c.Update(key, obj)`**, logically atomic, for an object meeting `OK` (with the accessor's
contract `rvAcc D rvOf` for the call's object, `D obj`): the items have `obj` at `key`, and the store's resource version becomes the
object's if its accessor has one (`rvOf obj`), whatever it was: **the resource version is not
kept monotone by the store**; it is the last written object's. -/
abbrev threadSafeMap.Update.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (D : GoInterface → IProp GF) (rvOf : GoInterface → Option GoString) (key : GoString) (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      rvAcc D rvOf ∗ □ D obj ∗ □ OK obj }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"Update")) (Val #key))
      (Val #obj))
    @@ ∅
  <<{ storeSt γ (σ.update key obj (rvOf obj)) }>>
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
