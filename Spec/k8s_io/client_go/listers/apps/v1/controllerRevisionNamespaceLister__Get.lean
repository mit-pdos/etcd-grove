/-
`controllerRevisionNamespaceLister.Get` (`listers/apps/v1/controllerrevision.go`, promoted from the embedded
`listers.ResourceIndexer[*v1.ControllerRevision]`): the generic lister's `Get`. Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

/-- The ControllerRevision namespace lister over the cache `ca`. -/
def crnlVal (ca : Loc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ns : GoString) :
    k8s_io.client_go.listers.apps.v1.controllerRevisionNamespaceLister :=
  ⟨riVal ca res ns⟩

/-- **`l.Get`** for the ControllerRevision namespace lister `l` over the cache `ca`: `ResourceIndexer.Get`'s spec at `X = v1.ControllerRevision`. -/
abbrev controllerRevisionNamespaceLister.Get.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (kf : GoFunc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ns : GoString) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ typedOK OK k8s_io.api.apps.v1.ControllerRevision.ty }}
  <<{ ∀∀ σ, storeSt γ σ ∗ ⌜noNil σ.items⌝ }>>
    (App (Val #(methods controllerRevisionNamespaceLister.ty go!"Get" #(crnlVal ca res ns))) (Val #name))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items⌝ }>>
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      getPost OK k8s_io.api.apps.v1.ControllerRevision.ty σ (nsKey ns name) r err ∗ tsReader ts γ OK Fam }}

end spec

end appslisters
end EtcdGrove
end Perennial
