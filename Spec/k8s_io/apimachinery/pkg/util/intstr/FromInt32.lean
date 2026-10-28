/-
`intstr.FromInt32(n)`: the trust boundary (names only; `IntOrString`'s struct is axiomatized, gap C5 of notes/k8s-clientgo-goose.md). Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.util.intstr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace intstr

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.intstr.Assumptions]

/-- `intstr.FromInt32(n)`: some `IntOrString` (its struct is axiomatized, gap C5). -/
abbrev FromInt32.spec : Prop :=
  ∀ (n : w32),
  {{ (True : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.util.intstr.FromInt32)) (Val #n))
  {{ (v : k8s_io.apimachinery.pkg.util.intstr.IntOrString), RET #v; True }}

end spec

end intstr
end EtcdGrove
end Perennial
