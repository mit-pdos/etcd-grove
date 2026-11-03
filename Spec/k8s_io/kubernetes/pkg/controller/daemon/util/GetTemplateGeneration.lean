/-
`util.GetTemplateGeneration(ds)` (`daemonset_util.go`): the template-generation annotation
parsed (`strconv.ParseInt`), `nil` if absent, an error if it does not parse. Lean-first; Stage 3,
track B.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.util.Assumptions]

/-- **`GetTemplateGeneration(ds)`**: a fresh `*int64` or `nil`, or an error. -/
abbrev GetTemplateGeneration.spec : Prop :=
  ∀ (ds : Loc) (d : kd.apps.DaemonSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util ∗ □ dsAt ds DFrac.discard d }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.util.GetTemplateGeneration)) (Val #ds))
  {{ (gp : Loc) (err : GoInterface), RET (PairV #gp #err); fmt.argOk err ∗
      ∃ gen, int64PtrD gp (DFrac.own 1) gen }}

end spec

end dsctl
end EtcdGrove
end Perennial
