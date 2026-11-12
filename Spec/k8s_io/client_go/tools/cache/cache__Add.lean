/-
`(*cache).Add(obj)` (`store.go`): the key function's key, then the thread-safe store's `Add`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the `cache` wrapper, `store.go`).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.Add(obj)`**, logically atomic: the object stored at its key (`KF obj`), the resource version the object's (`threadSafeMap.Add`).
The key function's (`keyOk D kf KF`) and the accessor's (`rvAcc D rvOf`) contracts are the call's: `D` covers the call's object (the client takes `D o := ⌜o = obj⌝`, `KF`, `rvOf` its key and version), as an object's key and version are functions of its contents in the heap. -/
abbrev cache.Add.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (D : GoInterface → IProp GF) (KF : GoInterface → GoString)
    (rvOf : GoInterface → Option GoString) (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      keyOk D kf KF ∗ rvAcc D rvOf ∗ □ D obj ∗ □ OK obj }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"Add")) (Val #obj))
    @@ ∅
  <<{ storeSt γ (σ.update (KF obj) obj (rvOf obj)) }>>
  {{ RET #interface.nil; True }}

end spec

end cache
end EtcdGrove
end Perennial
