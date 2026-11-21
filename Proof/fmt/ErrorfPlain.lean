/-
`fmt.Errorf` of a format without a `w` verb is `errors.New` of its message (`Spec/fmt/ErrorfPlain.lean`):
from Perennial's `fmt.wp_Errorf` (fmtmodel, 2026-11-20: Perennial's model formats, calls the
arguments' methods and returns `errors.New(s)` when no `%w` directive has an argument, as Go's
`errorf`; until then an axiom here).
-/
module

public import Spec.fmt.ErrorfPlain
public import Perennial.Proof.fmt
public import Proof.fmt.OutLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

theorem fmt.ErrorfPlain.wp_proof : fmt.ErrorfPlain.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq ⟨ds, hds, hnw⟩
  iintro %Φ ⟨#Hpkg, Hsl, Hok⟩ HΦ
  wp_apply (_root_.Perennial.fmt.wp_Errorf format args_sl xs dq) $$ [$Hpkg $Hsl $Hok]
    as %err ⟨Hsl, %s, %Hs, Herr⟩
  iunfold _root_.Perennial.fmt.errorfErr at Herr
  icases Herr with ⟨%-, #HE, Hcase⟩
  simp only [hds, _root_.Perennial.fmt.wrapArgs, fmt.wrapArgsFrom_noW hnw]
  icases Hcase with ⟨%x, %hx, #Hcell⟩
  subst hx
  iapply HΦ
  iframe
  iexists s
  isplitr
  · unfold errStrCell; iexact Hcell
  isplitr
  · ipureintro; exact fmt.SprintfOut_litPrefix Hs
  iexact HE

end proof

end EtcdGrove
end Perennial
