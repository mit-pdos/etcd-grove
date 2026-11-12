/-
`(*cache).AddIndexers(newIndexers)` (`store.go:345`): the thread-safe store's
(`threadSafeMap.AddIndexers`). Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__AddIndexers

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

/-- **`ca.AddIndexers(nm)`**, logically atomic: `threadSafeMap.AddIndexers`'. -/
abbrev cache.AddIndexers.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (nm : Loc) (dn : DFrac) (nfv : GMap GoString GoFunc)
    (nids : GMap GoString Nat),
  GMap.size nfv ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      nm ↦${dn} nfv ∗ fnsOk OK nfv (GMap.fmap Fam nids) }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"AddIndexers"))
      (Val #nm))
    @@ ∅
  <<{ storeSt γ (σ.addIx nids) }>>
  {{ (err : GoInterface), RET #err;
      ⌜(nameClash σ.fnIds nids ∧ err ≠ interface.nil) ∨
        (¬ nameClash σ.fnIds nids ∧ err = interface.nil)⌝ ∗ nm ↦${dn} nfv }}

end spec

end cache
end EtcdGrove
end Perennial
