/-
Proof of `Spec/k8s_io/utils/trace/FromContext.lean` over the real code (`k8s.io/utils/trace`
`be93311217bd`, `trace/trace.go:309-314`; prove-metrics3, 2026-11-21): `ctx.Value(ContextTraceKey{})`
asserted to `*Trace`.
-/
module

public import Spec.k8s_io.utils.trace.FromContext

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

theorem trace.FromContext.wp_proof : trace.FromContext.spec (GF := GF) (hG := hG) := by
  intro ctx
  wp_start as #Hv
  iunfold context.valueAt at Hv
  wp_auto
  wp_apply Hv as %w %hw
  rcases hw with hn | ⟨⟨t, rfl⟩, hb⟩
  · cases w with
    | nil =>
      wp_auto
      iapply HΦ
      ipureintro; left; rfl
    | ok wi =>
      have hne := hn wi rfl
      wp_auto
      simp only [hne, ↓reduceIte]
      wp_auto
      iapply HΦ
      ipureintro; left; rfl
  · wp_auto
    iapply HΦ
    ipureintro; right; exact hb

end proof

end EtcdGrove
end Perennial
