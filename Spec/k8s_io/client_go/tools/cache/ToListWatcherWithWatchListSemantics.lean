/-
`cache.ToListWatcherWithWatchListSemantics(lw, client)` (`listwatch.go`): the wrapper
`&listWatcherWithWatchListSemanticsWrapper{lw, ...}`, whose `ListWithContext`/`WatchWithContext`
are `lw`'s (promoted): `lwOk` carries over. Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerApi

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

/-- **`ToListWatcherWithWatchListSemantics(lw, client)`**: `lw`, wrapped. -/
abbrev ToListWatcherWithWatchListSemantics.spec : Prop :=
  ∀ (p : Loc) (lw : GoInterfaceOk) (client : GoInterface) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ ⌜GoInterface.ok lw = interface.mkOk (go.GoType.PointerType ListWatch.ty) #p⌝ ∗
      lwOk lw γa cfg r }}
    (App (App (Val (@! ToListWatcherWithWatchListSemantics)) (Val #p)) (Val #client))
  {{ (x : GoInterfaceOk), RET #(GoInterface.ok x); lwOk x γa cfg r }}

end spec

end cache
end EtcdGrove
end Perennial
