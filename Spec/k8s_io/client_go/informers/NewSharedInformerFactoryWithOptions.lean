/-
`informers.NewSharedInformerFactoryWithOptions(client, 0, options...)` with no option: the factory
(all namespaces, empty maps, no informer yet), and the callers' halves of its informers'
not-started tokens (`facNotStarted`, one per resource, decision R6). Lean-first; the DaemonSet run's
track A.
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

/-- **`NewSharedInformerFactoryWithOptions(client, 0)`**, no option. -/
abbrev NewSharedInformerFactoryWithOptions.spec : Prop :=
  ∀ (c : Loc) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → Nat → Fn GF) (opts : GoSlice)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers ∗
      clientsetAt c γa cfg false ∗ apiReader γa ∗ keysOk γa ∗ ⌜∀ r, Fams r 0 = nsIdxFn⌝ ∗
      opts ↦*{dq} ([] : List k8s_io.client_go.informers.SharedInformerOption) }}
    (App (App (App (Val (@! k8s_io.client_go.informers.NewSharedInformerFactoryWithOptions))
      (Val #(clientVal c))) (Val #(W64 0 : time.Duration))) (Val #opts))
  {{ (f : Loc) (γF : FacNames), RET #(facVal f);
      opts ↦*{dq} ([] : List k8s_io.client_go.informers.SharedInformerOption) ∗ isFactory f γF γa cfg Fams ∗
      [∗list] r ∈ resAll, facNotStarted γF r 1 }}

end spec

end informers
end EtcdGrove
end Perennial
