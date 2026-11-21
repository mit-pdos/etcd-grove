/-
Proof of `Spec/k8s_io/utils/trace/New.lean` over the real code (`k8s.io/utils/trace` `be93311217bd`,
`trace/trace.go:154-156`: `&Trace{name: name, startTime: time.Now(), fields: fields}`; prove-otel4,
2026-11-21; until then a trust-boundary axiom). Lean-first.
-/
module

public import Spec.k8s_io.utils.trace.New
public import Perennial.Spec.time.Now

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.trace.Assumptions]

theorem trace.New.wp_proof (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    trace.New.spec (GF := GF) (hG := hG) := by
  intro name fields
  wp_start as #Hpkg
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Now as %now -
  ihave %Hnn : ⌜«$r0_ptr» ≠ null⌝ $$ [«$r0»]
  · iapply typedPointsto_not_null $$ «$r0»
  iapply HΦ
  ipureintro
  exact Hnn

end proof

end EtcdGrove
end Perennial
