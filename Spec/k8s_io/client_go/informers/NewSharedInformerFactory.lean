/-
`informers.NewSharedInformerFactory(client, 0)` (`informers/factory.go`): the factory over the
model API server's clientset, default resync `0` (the driver's; a positive resync is out of scope:
the handlers' resyncs are not covered). The caller gives read access to the server's state
(`apiReader`), its writers' good keys (`keysOk`), the informers' feature gates
(`features.informerGates`) and the index relations of each resource's store by index name, the
namespace index's `MetaNamespaceIndexFunc`'s (`Fams r "namespace" = nsIdxFn`). It gets the callers' halves of
the not-started tokens of the factory's informers, one per resource (`facNotStarted`, decision R6),
which `Start` takes back. Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.informers.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informers

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`NewSharedInformerFactory(client, 0)`**: see the file header. -/
abbrev NewSharedInformerFactory.spec : Prop :=
  ∀ (c : Loc) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → GoString → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers ∗
      clientsetAt c γa cfg false ∗ apiReader γa ∗ keysOk γa ∗ features.informerGates ∗
      ⌜∀ r, Fams r go!"namespace" = nsIdxFn⌝ }}
    (App (App (Val (@! k8s_io.client_go.informers.NewSharedInformerFactory)) (Val #(clientVal c)))
      (Val #(W64 0 : time.Duration)))
  {{ (f : Loc) (γF : FacNames), RET #(facVal f); isFactory f γF γa cfg Fams ∗
      [∗list] r ∈ resAll, facNotStarted γF r 1 }}

end spec

end informers
end EtcdGrove
end Perennial
