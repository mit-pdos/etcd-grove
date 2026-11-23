/-
`zerolog`'s hypotheses as its functions' proofs (the linking tier, CLAUDE.md "Import tiers"): each
`<F>.wp_proof` is the field of the hypothesis class (`Spec.lean`) that states `<F>.spec`. A proof
file takes the class as an instance argument and uses its fields; only linking modules see these.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Spec

@[expose] public section

noncomputable section

namespace Perennial.github_com.rs.zerolog

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- The event specs (`Logger.{Trace,Debug,Info,Warn,Error}`, `Event.{Str,Int,...,Msg}`), for some
event token. -/
theorem events.wp_proof [h : Hyps GF] : ∃ ownEvent : Loc → IProp GF, EventSpecs GF ownEvent :=
  h.events
theorem ParseLevel.warn.wp_proof [h : Hyps GF] : ParseLevel.warn.spec (GF := GF) := h.ParseLevel_warn
theorem SetGlobalLevel.wp_proof [h : Hyps GF] : SetGlobalLevel.spec (GF := GF) := h.SetGlobalLevel
theorem New.wp_proof [h : Hyps GF] : New.spec (GF := GF) := h.New

end proof

end Perennial.github_com.rs.zerolog
