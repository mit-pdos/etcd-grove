/- Lean-first (no Rocq counterpart).

`fillDefault(model)` (checker.go): the model with its `nil` functions replaced by the
defaults (`Partition` by `noPartition`, `StepContext` by a closure over `Step`, ...).
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev fillDefault.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ isModel S m }}
    (App (Val (@! github_com.anishathalye.porcupine.fillDefault)) (Val #m))
  {{ (m' : Model), RET #m'; isModelFilled S m' ∗ noPartitionSpec m'.Partition' }}

end spec

end porcupine
end EtcdGrove
end Perennial
