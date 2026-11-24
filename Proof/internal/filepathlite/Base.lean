/-
Proof of `Spec/internal/filepathlite/Base.lean`. Lean-first.
-/
module

public import Spec.internal.filepathlite.Base
public import Spec.internal.filepathlite.IsPathSeparator
public import Spec.internal.filepathlite.VolumeName
public import Proof.internal.filepathlite.Lexical

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.internal.filepathlite.Assumptions]

set_option linter.unusedVariables false in
/-- From `Base.wp_lex` (`Lexical.lean`, which has the proof): `Base` needs no `isPkgInit`. -/
theorem filepathlite.Base.wp_proof
    (hSep : filepathlite.IsPathSeparator.spec (GF := GF) (hG := hG))
    (hVol : filepathlite.VolumeName.spec (GF := GF) (hG := hG)) :
    filepathlite.Base.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as #_
  wp_apply filepathlite.Base.wp_lex p as %r %hr
  iapply HΦ
  ipureintro
  exact hr

end proof

end EtcdGrove
end Perennial
