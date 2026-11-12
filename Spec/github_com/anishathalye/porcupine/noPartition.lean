/- Lean-first (no Rocq counterpart).

`noPartition(history)` (model.go): the one partition `[][]Operation{history}` (what
`fillDefault` stores for a `nil` `Partition`; `noPartitionSpec` of its function value).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev noPartition.spec : Prop :=
  ∀ (sl : GoSlice) (ops : List Operation) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ sl ↦*{dq} ops }}
    (App (Val (@! github_com.anishathalye.porcupine.noPartition)) (Val #sl))
  {{ (r : GoSlice), RET #r; r ↦* [sl] ∗ sl ↦*{dq} ops }}

end spec

end porcupine
end EtcdGrove
end Perennial
