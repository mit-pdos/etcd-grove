/- Lean-first (no Rocq counterpart).

`checkSingle(ctx, model, consistency, history, computePartial)` (dag.go, PR #46): the DAG search
over one partition (an `operationHistory` holding the chains `cs` of `h`). It answers `true` only
on a partition linearizable respecting the chains' order, and `false` only on one that is not,
or once its context is done. `longest` (for the visualizer) is memory only. The partition's memory
is not given back (the search writes `firstUnk`/`visited` into it).
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
abbrev checkSingle.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (ctx : GoInterfaceOk)
    (ctxd : context.ContextDesc (IProp GF)) (c : Consistency) (ohsl : GoSlice)
    (h : List (Theory.Op OpV)) (cs : List (List Nat)) (cp : Bool),
  ChainsOk h cs → HistWf h → AllocOk cs.length h.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isContext ctx ctxd ∗
      isModelFilled S m ∗ isLinearizability c ∗ ohistOwn ohsl h cs ∗ histIoOk S h }}
    (App (App (App (App (App (Val (@! github_com.anishathalye.porcupine.checkSingle))
      (Val #(GoInterface.ok ctx))) (Val #m)) (Val #c)) (Val #ohsl)) (Val #cp))
  {{ (b : Bool) (longest : GoSlice), RET (PairV #b #longest);
      (⌜b = true ∧ LinearizableCO S.M h (chainOrder cs)⌝ ∨
        (⌜b = false⌝ ∗ (⌜¬ LinearizableCO S.M h (chainOrder cs)⌝ ∨ □ ctxd.PDone))) ∗
      longestOwn longest h.length }}

end spec

end porcupine
end EtcdGrove
end Perennial
