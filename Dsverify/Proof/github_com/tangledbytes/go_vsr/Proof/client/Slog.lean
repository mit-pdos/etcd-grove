/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/client/Slog.lean (lab master 915f964;
notes/dsv-vr.md), and the lab's `network.argOk_of_errOrNil` (`VsrProof/Proof/network/Ghost.lean`).
-/
/-
`slog` with the arguments the client logs: the lab proved `Logger.Error`/`Debug` for arguments of
types without `Error`/`String` methods from its `slog` model (`touch`); here `log/slog` has no
model, so the client's proofs take the logger's specs as hypotheses (`log.slog.Logger.Error.spec`,
`log.slog.Logger.Debug.spec`, stated in `Proof/replica/LibHyps.lean` over `log.slog.argOk`, the
lab's arguments). This file proves the client's arguments `argOk`:
* `argOk_string`: a string;
* `argOk_noFmt`: a value of a type without formatting methods (`NoFmtArg`, `go_type_set`);
* `argOk_of_errOrNil`: an error result (`bufio.errOrNil`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.LibHyps
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.jsonlib

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace log.slog

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem argOk_string (s : GoString) :
    ⊢ argOk (GF := GF) (interface.mkOk go.string #s) := by
  unfold argOk
  ileft; ipureintro
  intro ii h
  simp [interface.mkOk] at h
  subst h
  exact ⟨fun _ => ⟨s, rfl⟩, fun hi => absurd hi fmt.not_isIntArgType_string, Or.inl (Or.inl rfl)⟩

theorem argOk_noFmt (v : GoInterface) (h : NoFmtArg v) :
    ⊢ argOk (GF := GF) v := by
  unfold argOk
  iright; iright; ipureintro
  exact h

theorem argOk_of_errOrNil (e : GoInterface) :
    bufio.errOrNil (GF := GF) e ⊢ argOk e := by
  unfold bufio.errOrNil argOk
  iintro (%he | ⟨#He, -⟩)
  · ileft; ipureintro
    intro ii h; subst he; cases h
  · iright; ileft; iexact He

end defs

end log.slog

end Perennial
