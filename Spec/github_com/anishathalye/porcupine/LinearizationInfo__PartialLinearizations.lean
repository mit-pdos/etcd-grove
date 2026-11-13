/- Lean-first (no Rocq counterpart).

`(*LinearizationInfo).PartialLinearizations()` (checker.go): the info's
`partialLinearizations` field (what `linInfoOk` describes after an `Ok` check).
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev LinearizationInfo.PartialLinearizations.spec : Prop :=
  ∀ (li : Loc) (dq : DFrac) (info : LinearizationInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ li ↦{dq} info }}
    (App (Val #(methods (go.GoType.PointerType github_com.anishathalye.porcupine.LinearizationInfo.ty)
      go!"PartialLinearizations" #li)) (Val #()))
  {{ RET #info.partialLinearizations'; li ↦{dq} info }}

end spec

end porcupine
end EtcdGrove
end Perennial
