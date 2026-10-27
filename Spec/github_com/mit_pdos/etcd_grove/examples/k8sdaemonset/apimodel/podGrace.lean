/-
`podGrace(o, opts)`: pod's `CheckGracefulDelete` (`podGraceD`).
Lean-first (no Rocq counterpart); phase 3 of `notes/k8s-daemonset-plan.md` (the model API server's
specs, D50's internal layer).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

abbrev podGrace.spec : Prop :=
  ∀ [ApiDeps] (x : GoInterface) (d : kd.core.Pod) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions)
    (dq : DFrac) (dop : kd.meta.DeleteOptions),
  {{ (objAt x (DFrac.own 1) (.pod d) : IProp GF) ∗ kd.meta.DeleteOptions.own opts dq dop }}
    (App (App (Val (@! apimodel.podGrace)) (Val #x)) (Val #opts))
  {{ RET #(podGraceD d dop.GracePeriodSeconds'); objAt x (DFrac.own 1) (.pod d) ∗
      kd.meta.DeleteOptions.own opts dq dop }}

end spec

end apimodel
end EtcdGrove
end Perennial
