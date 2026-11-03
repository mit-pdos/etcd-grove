/- Lean-first (no Rocq counterpart).

`checkOperations(model, consistency, history, verbose, timeout)` (checker.go, PR #46):
`fillDefault`, the model's `Partition` (`noPartition`: the one partition `[history]`), the client
count (`maxClientId + 1`), `makeEntries` per partition, `checkParallel`, here with a consistency
that is linearizability (`isLinearizability`: what the public entry points pass). The three
outcomes, as `CheckOperationsTimeout`'s.
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
abbrev checkOperations.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (c : Consistency) (sl : GoSlice)
    (ops : List Operation) (dq : DFrac) (verbose : Bool) (dur : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ isLinearizability c ∗ sl ↦*{dq} ops ∗ opsIoOk S ops ∗
      ⌜HistOk ops⌝ ∗ ⌜ClientsOk ops⌝ }}
    (App (App (App (App (App (Val (@! github_com.anishathalye.porcupine.checkOperations))
      (Val #m)) (Val #c)) (Val #sl)) (Val #verbose)) (Val #dur))
  {{ (r : GoString) (info : LinearizationInfo), RET (PairV #r #info);
      ⌜(r = go!"Ok" ∧ LinearizableCO S.M (histOf ops) (clientOrder ops)) ∨
        (r = go!"Illegal" ∧ ¬ LinearizableCO S.M (histOf ops) (clientOrder ops)) ∨
        (r = go!"Unknown" ∧ 0 < sint.Z dur)⌝ ∗ sl ↦*{dq} ops }}

end spec

end porcupine
end EtcdGrove
end Perennial
