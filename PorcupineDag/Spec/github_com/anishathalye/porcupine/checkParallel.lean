/- Lean-first (no Rocq counterpart).

`checkParallel(model, consistency, history, entries, computeInfo, timeout)` (checker.go, PR #46):
one `checkSingle` goroutine per partition (an `operationHistory`, with its chains `cs`), under a
context cancelled when a partition fails (unless `computeInfo`) or at the timeout. It answers `Ok`
only if every partition is linearizable respecting its chains' order, `Illegal` only if one is
not, `Unknown` only with a timeout. The partitions' memory is handed to the goroutines (not given
back); `entries` is not read; `LinearizationInfo` has no claim.
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
abbrev checkParallel.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (c : Consistency) (hsl : GoSlice)
    (ohsls : List GoSlice) (hs : List (List (Theory.Op OpV))) (css : List (List (List Nat)))
    (esl : GoSlice) (cp : Bool) (dur : w64),
  ohsls.length = hs.length → css.length = hs.length → (hs.length : Int) < 2 ^ 32 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModelFilled S m ∗ isLinearizability c ∗ hsl ↦*□ ohsls ∗
      ([∗list] i ↦ ohsl ∈ ohsls, ∃ (h : List (Theory.Op OpV)) (cs : List (List Nat)),
        ⌜hs[i]? = some h ∧ css[i]? = some cs ∧ ChainsOk h cs ∧ HistWf h ∧
          AllocOk cs.length h.length⌝ ∗
        ohistOwn ohsl h cs ∗ histIoOk S h) }}
    (App (App (App (App (App (App (Val (@! github_com.anishathalye.porcupine.checkParallel))
      (Val #m)) (Val #c)) (Val #hsl)) (Val #esl)) (Val #cp)) (Val #dur))
  {{ (r : GoString) (info : LinearizationInfo), RET (PairV #r #info);
      ⌜(r = go!"Ok" ∧ ∀ (i : Nat) h cs, hs[i]? = some h → css[i]? = some cs →
          LinearizableCO S.M h (chainOrder cs)) ∨
        (r = go!"Illegal" ∧ ¬ ∀ (i : Nat) h cs, hs[i]? = some h → css[i]? = some cs →
          LinearizableCO S.M h (chainOrder cs)) ∨
        (r = go!"Unknown" ∧ 0 < sint.Z dur)⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
