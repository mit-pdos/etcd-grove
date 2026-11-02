/- Lean-first (no Rocq counterpart).

`CheckOperationsVerbose(model, history, timeout)` (porcupine.go), what etcd's robustness
tests call (`validateLinearizableOperationsAndVisualize`): it answers `Ok` only on a
linearizable history, `Illegal` only on one that is not (a failing test is a real bug), and
`Unknown` only with a timeout (`timeout > 0`): with no timeout it decides linearizability.

`context.isClosedchanInit` (`context`'s package-init ghost fact: `closedchan` is closed) is what
`checkParallel`'s `context.WithCancel(context.Background())` needs.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Defs

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
abbrev CheckOperationsVerbose.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac) (dur : w64),
  HistOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperationsVerbose))
      (Val #m)) (Val #sl)) (Val #dur))
  {{ (r : GoString) (info : LinearizationInfo), RET (PairV #r #info);
      ⌜(r = go!"Ok" ∧ Linearizable S.M (histOf ops)) ∨
        (r = go!"Illegal" ∧ ¬ Linearizable S.M (histOf ops)) ∨
        (r = go!"Unknown" ∧ 0 < sint.Z dur)⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
