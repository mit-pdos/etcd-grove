/- Lean-first (no Rocq counterpart).

`newChains(history, consistency)` (dag.go, PR #46): the chains of a partition (an
`operationHistory` holding the chains `cs` of `h`) at no operation linearized: heads 0, every
non-empty chain's first operation visited, the `nDeps`, and the frontier the sorted candidates
(`ChainsInv h cs []`). The `firstUnk` slices are pieces of one array of `n·numClients` ints.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ChainsOwn

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
abbrev newChains.spec : Prop :=
  ∀ (ohsl : GoSlice) (h : List (Theory.Op OpV)) (cs : List (List Nat)) (cons : Consistency),
  ChainsOk h cs → HistWf h → AllocOk cs.length h.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ ohistOwn ohsl h cs ∗ isLinearizability cons }}
    (App (App (Val (@! github_com.anishathalye.porcupine.newChains)) (Val #ohsl)) (Val #cons))
  {{ (chV : chains), RET #chV; ∃ st : ChSt, chainsRepr chV h cs st ∗ ⌜ChainsInv h cs [] st⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
