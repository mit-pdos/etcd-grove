/- Lean-first (no Rocq counterpart).

`(*chains).computeFirstUnk(c, consistency)` (dag.go, PR #46): if client `c`'s head operation is
not visited, its `firstUnk` for every other client `d` becomes `FUe` (the exponential, binary and
linear searches, from the previous operation's bound), and it is visited. Every visited
operation's `firstUnk` stays exact (`FuOk`). The clients slice is untouched (`chainsOwnCl`).
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
abbrev chains.computeFirstUnk.spec : Prop :=
  ∀ (ch : Loc) (cl : GoSlice) (h : List (Theory.Op OpV)) (cs : List (List Nat)) (st : ChSt) (c : w64)
    (cons : Consistency),
  ChainsOk h cs → HistWf h → ShapeOk cs st → FuOk h cs st → HeadsOk cs st.heads →
  0 ≤ sint.Z c → sint.nat c < cs.length →
  (0 < st.head (sint.nat c) → st.head (sint.nat c) < (chain cs (sint.nat c)).length →
    st.visAt (sint.nat c) (st.head (sint.nat c) - 1) = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ chainsOwnCl ch cl h cs st ∗ isLinearizability cons }}
    (App (App (Val (ch @!! go.GoType.PointerType chains.ty @!! go!"computeFirstUnk")) (Val #c))
      (Val #cons))
  {{ RET #(); ∃ st' : ChSt, chainsOwnCl ch cl h cs st' ∗
      ⌜st'.heads = st.heads ∧ st'.nDeps = st.nDeps ∧ st'.frontier = st.frontier ∧
        ShapeOk cs st' ∧ FuOk h cs st' ∧
        ∀ c' k, st'.visAt c' k = (st.visAt c' k ||
          decide (c' = sint.nat c ∧ k = st.head c' ∧ k < (chain cs c').length))⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
