/-
`NewDaemonSetLister(indexer)` (`listers/apps/v1/daemonset.go:45`): the DaemonSet lister over
`indexer`, a `*daemonSetLister` holding `listers.New[*DaemonSet](indexer, Resource("daemonset"))`.
Lean-first.
-/
module

public import Proof.k8s_io.client_go.listers.Defs
public import GeneratedProof.k8s_io.client_go.listers.apps.v1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI k8s_io.client_go.listers.apps.v1

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]

/-- **`NewDaemonSetLister(idx)`** returns a fresh `*daemonSetLister` whose lister is over `idx`, not
namespaced (its `GroupResource` is `Resource`'s, unspecified). -/
abbrev NewDaemonSetLister.spec : Prop :=
  ∀ (idx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 }}
    (App (Val (@! k8s_io.client_go.listers.apps.v1.NewDaemonSetLister)) (Val #idx))
  {{ (l : Loc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
      RET #(interface.mkOk (go.GoType.PointerType daemonSetLister.ty) #l);
      l.[daemonSetLister, go!"ResourceIndexer"] ↦ (⟨idx, res, []⟩ : k8s_io.client_go.listers.ResourceIndexer Loc) }}

end spec

end appslisters
end EtcdGrove
end Perennial
