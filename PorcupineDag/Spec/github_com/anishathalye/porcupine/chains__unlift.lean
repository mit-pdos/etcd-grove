/- Lean-first (no Rocq counterpart).

`(*chains).unlift(stack, serialized, consistency)` (dag.go, PR #46): pop the newest frame `f`:
its client's head moves back, the bitset loses it, the `nDeps` and the frontier are those of the
frames below (so the frontier, mapped to the head operations, is the candidate list `f.fr` the
frame was lifted from: `candList_unique`); it returns the frame's state value and position.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Search

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev chains.unlift.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (np : NaInvPoolName) (cons : Consistency)
    (h : List (Theory.Op OpV)) (cs : List (List Nat)) (ch stack_ptr lin_ptr cm : Loc)
    (f : Theory.Frame σ) (fs : List (Theory.Frame σ)) (fr : List Nat)
    (cache : List ((Nat → Prop) × σ)) (s : σ) (p : Int),
  ChainsOk h cs → HistWf h → AllocOk cs.length h.length →
  Struct S.M h cs (Before h cs) (f :: fs) s fr p →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ isLinearizability cons ∗
      searchOwn S np h cs ch stack_ptr lin_ptr cm (f :: fs) fr cache }}
    (App (App (App (Val (ch @!! go.GoType.PointerType chains.ty @!! go!"unlift"))
      (Val #stack_ptr)) (Val #lin_ptr)) (Val #cons))
  {{ (sv : GoInterface) (idx : w64), RET (PairV #sv #idx);
      searchOwn S np h cs ch stack_ptr lin_ptr cm fs f.fr cache ∗ shared S np fs.length sv f.pre ∗ ⌜sint.Z idx = f.pos⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
