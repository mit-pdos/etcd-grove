/-
`metav1.Now()` (`time.go`): some time. Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.apis.«meta».v1
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metav1

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

/-- `metav1.Now()`: some time (`Time{time.Now()}`). -/
abbrev Now.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
    (App (Val (@! k8s_io.apimachinery.pkg.apis.«meta».v1.Now)) (Val #()))
  {{ (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time), RET #t; True }}

end spec

end metav1
end EtcdGrove
end Perennial
