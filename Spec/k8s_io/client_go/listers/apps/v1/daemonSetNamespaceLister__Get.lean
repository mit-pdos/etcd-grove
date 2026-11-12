/-
`daemonSetNamespaceLister.Get(name)` (`listers/apps/v1/daemonset.go`, promoted from the embedded
`listers.ResourceIndexer[*v1.DaemonSet]`): the generic lister's `Get`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.ResourceIndexer__Get
public import GeneratedProof.k8s_io.client_go.listers.apps.v1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI cache listers k8s_io.client_go.listers.apps.v1

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

/-- The DaemonSet namespace lister over the cache `ca`. -/
def dsnlVal (ca : Loc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ns : GoString) :
    k8s_io.client_go.listers.apps.v1.daemonSetNamespaceLister :=
  ⟨riVal ca res ns⟩

/-- **`l.Get(name)`** for the DaemonSet namespace lister `l` over the cache `ca`:
`ResourceIndexer.Get`'s spec at `X = v1.DaemonSet`. -/
abbrev daemonSetNamespaceLister.Get.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ns name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ typedOK OK k8s_io.api.apps.v1.DaemonSet.ty }}
  <<{ ∀∀ σ, storeSt γ σ ∗ ⌜noNil σ.items⌝ }>>
    (App (Val #(methods daemonSetNamespaceLister.ty go!"Get" #(dsnlVal ca res ns))) (Val #name))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items⌝ }>>
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      getPost OK k8s_io.api.apps.v1.DaemonSet.ty σ (nsKey ns name) r err ∗ tsReader ts γ OK Fam }}

end spec

end appslisters
end EtcdGrove
end Perennial
