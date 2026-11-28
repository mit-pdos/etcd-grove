/-
`runtime.SchemeBuilder.Register(funcs...)` (`k8s.io/apimachinery/pkg/runtime/scheme_builder.go:37`:
`for _, f := range funcs { *sb = append(*sb, f) }`; prove-metav1, 2026-11-27: translated with its
body, the callee of metav1's translated `init.1`, `localSchemeBuilder.Register(RegisterConversions)`).
Lean-first; proved in `Proof/k8s_io/apimachinery/pkg/runtime/SchemeBuilder__Register.lean`.
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.runtime

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]

/-- `sb.Register(funcs...)` of a builder `*sb` holding the functions `xs` (with its capacity) and
`funcs` holding `fs` (at any fraction): `*sb` holds `xs ++ fs`, `funcs` unchanged. -/
abbrev runtime.SchemeBuilder.Register.spec : Prop :=
  ∀ (sb : Loc) (s : GoSlice) (xs : List GoFunc) (funcs : GoSlice) (fs : List GoFunc) (dq : DFrac),
  {{ (sb ↦ s ∗ s ↦* xs ∗ ownSliceCap GoFunc s (DFrac.own 1) ∗ funcs ↦*{dq} fs : IProp GF) }}
    (App (Val (sb @!! go.GoType.PointerType k8s_io.apimachinery.pkg.runtime.SchemeBuilder.ty @!!
      go!"Register")) (Val #funcs))
  {{ RET #(); ∃ s' : GoSlice, sb ↦ s' ∗ s' ↦* (xs ++ fs) ∗ ownSliceCap GoFunc s' (DFrac.own 1) ∗
      funcs ↦*{dq} fs }}

end spec

end EtcdGrove
end Perennial
