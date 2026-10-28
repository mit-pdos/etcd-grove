/- Lean-first (no Rocq counterpart).

`makeEntries(history)` (checker.go): the call and return entries of a history's
operations, numbered by their index, sorted by time with calls before returns at equal times
(`sort.Sort(byTime(entries))`).
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
abbrev makeEntries.spec : Prop :=
  ∀ (sl : GoSlice) (ops : List Operation) (dq : DFrac),
  HistOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ sl ↦*{dq} ops }}
    (App (Val (@! github_com.anishathalye.porcupine.makeEntries)) (Val #sl))
  {{ (esl : GoSlice), RET #esl;
      ∃ es, esl ↦* es ∗ ⌜EntriesFor (histOf ops) es⌝ ∗ sl ↦*{dq} ops }}

end spec

end porcupine
end EtcdGrove
end Perennial
