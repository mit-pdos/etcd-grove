/-
`(*sharedIndexInformer).GetStore()`: `s.indexer`, the informer's store. Lean-first; the DaemonSet
run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.SIIAt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`s.GetStore()`**: the store. -/
abbrev sharedIndexInformer.GetStore.spec : Prop :=
  ∀ (s : Loc) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res) (I : InfH) (Fam : Nat → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ siiAt s γa cfg r I Fam }}
    (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"GetStore")) (Val #()))
  {{ RET #(storeVal I); True }}

end spec

end cache
end EtcdGrove
end Perennial
