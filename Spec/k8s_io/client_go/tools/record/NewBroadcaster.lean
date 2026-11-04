/-
`record.NewBroadcaster(opts...)` (`tools/record`, names only): an event broadcaster
(`bcastOk`). The trust boundary: the events are a trusted no-op for the DaemonSet run (they do not
affect safety, `notes/k8s-daemonset-plan.md`, "The cut"; the model's event client drops them).
Lean-first, track C of the DaemonSet run.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- `record.NewBroadcaster(opts...)`: a broadcaster. -/
abbrev record.NewBroadcaster.spec : Prop :=
  ∀ (opts : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.record }}
    (App (Val (@! k8s_io.client_go.tools.record.NewBroadcaster)) (Val #opts))
  {{ (eb : GoInterface), RET #eb; bcastOk eb }}

end spec

end dsctl
end EtcdGrove
end Perennial
