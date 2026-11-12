/- Lean-first (no Rocq counterpart).

`(*chains).isComplete()` (dag.go, PR #46): whether every client's head is at its chain's end.
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
abbrev chains.isComplete.spec : Prop :=
  ∀ (ch : Loc) (h : List (Theory.Op OpV)) (cs : List (List Nat)) (st : ChSt),
  ShapeOk cs st → HeadsOk cs st.heads →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ chainsOwn ch h cs st }}
    (App (Val (ch @!! go.GoType.PointerType chains.ty @!! go!"isComplete")) (Val #()))
  {{ RET #(decide (∀ c, c < cs.length → st.head c = (chain cs c).length)); chainsOwn ch h cs st }}

end spec

end porcupine
end EtcdGrove
end Perennial
