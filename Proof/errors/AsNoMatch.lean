/-
`errors.As` of an error in whose tree, to depth one, nothing matches the target's element type
(`nil`, a leaf, or a wrapper unwrapping once to `nil` or a leaf): an instance of the no-match case
of Perennial's proved `errors.As` (`errors.wp_As`, `As` translated from its Go model since Perennial
52d62e83c), at depth one (`asNoMatch T 1`). Until the pin bump to it, an axiom here (the trust
boundary; the reasoning, the Go source lines and the evidence are in `Spec/errors/AsNoMatch.lean`'s
header and `notes/axiom-review/asnomatch.md`). It replaces `errors.AsLeafTy` (its leaf case,
`Proof/errors/AsLeafTy.lean`) and the four `apierrors` checks' axioms (prove-k8s2, 2026-11-20).
-/
module

public import Spec.errors.AsNoMatch
public import Perennial.Proof.errors.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section pure
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- A dynamic type outside `T`'s type set and, for a non-interface `T`, of another underlying type is
not assignable to `T`, and the model decides it. -/
theorem errors.asNoMatch_notAssignable {T : go.GoType} {ii : GoInterfaceOk}
    (hts : go.typeSetContains ii.ty T = false)
    (hu : go.isInterfaceType (underlying T) = false → underlying ii.ty ≠ underlying T) :
    _root_.Perennial.errors.asAssignable T ii = false ∧ _root_.Perennial.errors.AsDecided T ii := by
  refine ⟨?_, fun hI => ⟨fun heq => absurd (congrArg underlying heq) (hu hI), fun _ => hu hI⟩⟩
  unfold _root_.Perennial.errors.asAssignable
  cases hI : go.isInterfaceType (underlying T)
  · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not]
    exact fun heq => hu hI (congrArg underlying heq)
  · simpa using hts

theorem errors.asNoMatchLeaf_perennial {T : go.GoType} {e : GoInterface}
    (h : errors.asNoMatchLeaf T e) : _root_.Perennial.errors.asNoMatchLeaf T e := by
  rcases h with h | ⟨ii, rfl, hleaf, hts, hu⟩
  · exact Or.inl h
  · exact Or.inr ⟨ii, rfl, hleaf, errors.asNoMatch_notAssignable hts hu⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

theorem errors.AsNoMatch.wp_proof : errors.AsNoMatch.spec (GF := GF) (hG := hG) := by
  intro err l T' _ _ T _ v hT
  iintro %Φ ⟨Hinit, Hl, Hno⟩ HΦ
  wp_apply (_root_.Perennial.errors.wp_As.2.2 1 err l v hT) $$ [Hinit Hl Hno] as Hl
  · iframe
    simp only [_root_.Perennial.errors.asNoMatch, errors.asNoMatchWrap]
    icases Hno with (%Hleaf | ⟨%ii, %Hw, Hun⟩)
    · ileft
      ipureintro
      exact errors.asNoMatchLeaf_perennial Hleaf
    · iright
      obtain ⟨Herr, Hts, Hu, HAs, HUnwrap⟩ := Hw
      obtain ⟨Hna, Hdec⟩ := errors.asNoMatch_notAssignable Hts Hu
      iexists ii
      isplitr
      · ipureintro
        exact ⟨Herr, Hna, Hdec, HAs, HUnwrap⟩
      iintro %Ψ HΨ
      iapply Hun
      iintro %e %He
      iapply HΨ
      ipureintro
      exact errors.asNoMatchLeaf_perennial He
  iapply HΦ
  iexact Hl

end proof

end EtcdGrove
end Perennial
