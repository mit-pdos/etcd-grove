/- Lean-first (no Rocq counterpart).

`(*Consistency).Check(a, b)` (consistency.go, PR #46), on linearizability (`isLinearizability`):
the fold of `RealTime`'s and `GeneralLikely`'s answers on `a.Op`, `b.Op` (`linOrder`), and no
error (the conflict error, and its `%+v` formatting, are unreachable: `RealTime` gives at most one
hard order, `GeneralLikely` none).
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
abbrev Consistency.Check.spec : Prop :=
  ∀ (cp : Loc) (c : Consistency) (dqc : DFrac) (pa pb : Loc) (a b : clientOperation)
    (dqa dqb : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ cp ↦{dqc} c ∗ isLinearizability c ∗ pa ↦{dqa} a ∗ pb ↦{dqb} b }}
    (App (App (Val (cp @!! go.GoType.PointerType Consistency.ty @!! go!"Check")) (Val #pa))
      (Val #pb))
  {{ RET (PairV #(linOrder a.Op' b.Op') #interface.nil);
      cp ↦{dqc} c ∗ pa ↦{dqa} a ∗ pb ↦{dqb} b }}

end spec

end porcupine
end EtcdGrove
end Perennial
