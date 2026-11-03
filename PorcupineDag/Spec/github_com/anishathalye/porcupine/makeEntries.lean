/- Lean-first (no Rocq counterpart).

`makeEntries(history, numClients)` (checker.go, PR #46): the history's call and return entries,
sorted by time (no longer read by anything: no claim), and its operations split by client, in the
order listed (`ohistOwn` of `chainsOf`). The client ids index the `numClients` slices; the
allocation bound is twice what `makeEntries` alone needs (`24·numClients` bytes), what its caller
has.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev makeEntries.spec : Prop :=
  ∀ (sl : GoSlice) (ops : List Operation) (dq : DFrac) (nc : w64),
  HistOk ops → 0 ≤ sint.Z nc → AllocOk (sint.nat nc) ops.length →
  (∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' ∧ sint.Z o.ClientId' < sint.Z nc) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ sl ↦*{dq} ops }}
    (App (App (Val (@! github_com.anishathalye.porcupine.makeEntries)) (Val #sl)) (Val #nc))
  {{ (esl ohsl : GoSlice), RET (PairV #esl #ohsl);
      (∃ es : List entry, esl ↦* es) ∗
      ohistOwn ohsl (histOf ops) (chainsOf ops (sint.nat nc)) ∗ sl ↦*{dq} ops }}

end spec

end porcupine
end EtcdGrove
end Perennial
