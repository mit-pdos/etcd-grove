/- Lean-first (no Rocq counterpart).

`(*chains).removeFromFrontier(c)` (dag.go, PR #46): the frontier without `c` (its first
occurrence; `c` may be absent). The clients slice is untouched (`chainsOwnCl`).
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
abbrev chains.removeFromFrontier.spec : Prop :=
  ∀ (ch : Loc) (cl : GoSlice) (h : List (Theory.Op OpV)) (cs : List (List Nat)) (st : ChSt) (c : w64),
  0 ≤ sint.Z c → (∀ v ∈ st.frontier, v < cs.length) → (cs.length : Int) < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ chainsOwnCl ch cl h cs st }}
    (App (Val (ch @!! go.GoType.PointerType chains.ty @!! go!"removeFromFrontier")) (Val #c))
  {{ RET #(); chainsOwnCl ch cl h cs { st with frontier := st.frontier.erase (sint.nat c) } }}

end spec

end porcupine
end EtcdGrove
end Perennial
