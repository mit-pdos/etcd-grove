/- Lean-first (no Rocq counterpart).

`CheckOperations(model, history)` (porcupine.go, PR #46): `true` exactly on a history linearizable
by an order that also keeps each client's operations in the order listed (`LinearizableCO` at
`clientOrder`), for a history whose client ids index the chains and whose clients' returns do not
decrease in the order listed (`ClientsOk`, `notes/porcupine-dag-plan.md`). Under sequential
clients this is v1.3.1's spec (`Results.lean`, `CheckOperations.spec_seq`). The caller's slice is
given back (the checker's goroutines read copies of the operations).

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
abbrev CheckOperations.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops ∗
      ⌜HistOk ops⌝ ∗ ⌜ClientsOk ops⌝ }}
    (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperations))
      (Val #m)) (Val #sl))
  {{ (b : Bool), RET #b; ⌜b = true ↔ LinearizableCO S.M (histOf ops) (clientOrder ops)⌝ ∗
      sl ↦*{dq} ops }}

end spec

end porcupine
end EtcdGrove
end Perennial
