/- Lean-first (no Rocq counterpart).

`CheckOperationsTimeout(model, history, timeout)` (porcupine.go, PR #46): `Ok` only on a
history linearizable respecting the client order (`LinearizableCO`), `Illegal` only on one that
is not, `Unknown` only with a timeout (`timeout > 0`); under `ClientsOk` (see `CheckOperations`).
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
abbrev CheckOperationsTimeout.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac) (dur : w64),
  HistOk ops → ClientsOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperationsTimeout))
      (Val #m)) (Val #sl)) (Val #dur))
  {{ (r : GoString), RET #r;
      ⌜(r = go!"Ok" ∧ LinearizableCO S.M (histOf ops) (clientOrder ops)) ∨
        (r = go!"Illegal" ∧ ¬ LinearizableCO S.M (histOf ops) (clientOrder ops)) ∨
        (r = go!"Unknown" ∧ 0 < sint.Z dur)⌝ ∗ sl ↦*{dq} ops }}

end spec

end porcupine
end EtcdGrove
end Perennial
