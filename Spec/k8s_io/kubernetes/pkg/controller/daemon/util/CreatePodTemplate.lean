/-
`util.CreatePodTemplate(template, generation, hash)` (`daemonset_util.go`): a deep copy of the
template with the daemon pods' tolerations and the generation and hash labels (`createTmplD`).
Lean-first; Stage 3, track B.
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

/-- **`CreatePodTemplate(t, gen, hash)`**: a fresh template, `createTmplD`; the arguments come back. -/
abbrev CreatePodTemplate.spec : Prop :=
  ∀ (v : k8s_io.api.core.v1.PodTemplateSpec) (dq : DFrac) (t : kd.core.PodTemplateSpec)
    (gp : Loc) (dqg : DFrac) (gen : Option w64) (hash : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util ∗ kd.core.PodTemplateSpec.own v dq t ∗
      int64PtrD gp dqg gen }}
    (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.util.CreatePodTemplate)) (Val #v)) (Val #gp)) (Val #hash))
  {{ (v' : k8s_io.api.core.v1.PodTemplateSpec), RET #v'; kd.core.PodTemplateSpec.own v dq t ∗
      int64PtrD gp dqg gen ∗
      kd.core.PodTemplateSpec.own v' (DFrac.own 1) (createTmplD t gen hash) }}

end spec

end dsctl
end EtcdGrove
end Perennial
