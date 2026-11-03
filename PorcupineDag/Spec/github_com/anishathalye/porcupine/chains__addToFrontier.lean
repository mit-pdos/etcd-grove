/- Lean-first (no Rocq counterpart).

`(*chains).addToFrontier(c, consistency)` (dag.go, PR #46): `c` inserted into the frontier
before the first member its head operation is `KeyGt` than (a later call, or the same call and a
larger client: `Check`'s `SoftAfter`, or `DontKnow` with `c > v`). On a frontier sorted by `KeyGt`
whose members' head operations are unrelated to `c`'s in real time (so `Check` never answers a
hard order), the result is sorted and its members are the old ones and `c`. The clients slice is untouched (`chainsOwnCl`).
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
abbrev chains.addToFrontier.spec : Prop :=
  ∀ (ch : Loc) (cl : GoSlice) (h : List (Theory.Op OpV)) (cs : List (List Nat)) (st : ChSt) (c : w64)
    (cons : Consistency),
  ChainsOk h cs → ShapeOk cs st → (cs.length : Int) < 2 ^ 62 →
  0 ≤ sint.Z c → sint.nat c < cs.length → st.head (sint.nat c) < (chain cs (sint.nat c)).length →
  sint.nat c ∉ st.frontier →
  (∀ v ∈ st.frontier, v < cs.length ∧ st.head v < (chain cs v).length ∧
    ¬ Prec h (hdOp cs st (sint.nat c)) (hdOp cs st v) ∧
    ¬ Prec h (hdOp cs st v) (hdOp cs st (sint.nat c))) →
  (frOf cs st).Pairwise (KeyGt h cs) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ chainsOwnCl ch cl h cs st ∗ isLinearizability cons }}
    (App (App (Val (ch @!! go.GoType.PointerType chains.ty @!! go!"addToFrontier")) (Val #c))
      (Val #cons))
  {{ RET #(); ∃ fr' : List Nat, chainsOwnCl ch cl h cs { st with frontier := fr' } ∗
      ⌜(fr'.map (hdOp cs st)).Pairwise (KeyGt h cs) ∧
        ∀ x, x ∈ fr' ↔ x = sint.nat c ∨ x ∈ st.frontier⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
