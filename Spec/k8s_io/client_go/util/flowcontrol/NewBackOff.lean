/-
`flowcontrol.NewBackOff(initial, max)` (`util/flowcontrol/backoff.go`, with body): a backoff over
the real clock, with no jitter and no entries. Lean-first, track C of the DaemonSet run.
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
variable [fc_sem : k8s_io.client_go.util.flowcontrol.Assumptions]

/-- `NewBackOff(initial, max)`: a backoff `isBackoff` describes. -/
abbrev flowcontrol.NewBackOff.spec : Prop :=
  ∀ (initial max : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.flowcontrol }}
    (App (App (Val (@! k8s_io.client_go.util.flowcontrol.NewBackOff)) (Val #initial)) (Val #max))
  {{ (b : Loc), RET #b; isBackoff b }}

end spec

end dsctl
end EtcdGrove
end Perennial
