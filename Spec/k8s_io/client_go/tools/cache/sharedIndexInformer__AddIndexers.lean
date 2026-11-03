/-
`(*sharedIndexInformer).AddIndexers(indexers)`: under `startedLock`, an error once stopped,
else the store's `AddIndexers`: on success each index registered for good (`infIdx`). Lean-first;
the DaemonSet run's track A.
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

/-- **`s.AddIndexers(m)`**: see the file header. -/
abbrev sharedIndexInformer.AddIndexers.spec : Prop :=
  ∀ (s : Loc) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res) (I : InfH) (Fam : Nat → Fn GF) (nm : Loc) (dn : DFrac) (nfv : GMap GoString GoFunc) (nids : GMap GoString Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ siiAt s γa cfg r I Fam ∗ ⌜GMap.size nfv ≤ 2 ^ 62⌝ ∗ nm ↦${dn} nfv ∗
      fnsOk (infObj I.γi r) nfv (GMap.fmap Fam nids) }}
    (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"AddIndexers")) (Val #nm))
  {{ (err : GoInterface), RET #err; nm ↦${dn} nfv ∗
      (⌜err ≠ interface.nil⌝ ∨ (⌜err = interface.nil⌝ ∗ [∗map] n ↦ j ∈ nids, infIdx I n j)) }}

end spec

end cache
end EtcdGrove
end Perennial
