/-
`controller.ComputeHash(template, collisionCount)` (`controller_utils.go`; gap D2: its body is
`ComputeHash_body.lean`): fnv-32a over `spew`'s dump of the template (`hashutil.DeepHashObject`),
then the collision count's bytes, `SafeEncodeString` of the decimal sum. Lean-first; Stage 3,
track B. Its value is `computeHashD` (`Scene.lean`). **Boundary**: `dump.ForHash`, `fnv`'s
`New32a`/`Write`/`Sum32`, `rand.SafeEncodeString` (names only) are trust-boundary specs to propose
(deterministic functions of their inputs); the proof rests on them.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.Defs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel k8s_io.kubernetes.pkg.controller

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

/-- **`ComputeHash(t, cc)`**: `computeHashD`. -/
abbrev ComputeHash.spec : Prop :=
  ∀ (tp : Loc) (dq : DFrac) (t : kd.core.PodTemplateSpec) (cp : Loc) (dqc : DFrac) (cc : Option w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ tmplAt tp dq t ∗
      int32PtrD cp dqc cc }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.controller.ComputeHash)) (Val #tp)) (Val #cp))
  {{ RET #((computeHashD t cc).val); tmplAt tp dq t ∗
      int32PtrD cp dqc cc }}

end spec

end dsctl
end EtcdGrove
end Perennial
