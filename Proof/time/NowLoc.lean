/-
The proof of `Spec/time/NowLoc.lean` (`time.Now.specLoc`), over Perennial's translation of Go's
`Now` and the trusted model of `runtimeNow`, as Perennial's `time.Now.wp_proof`. Lean-first.
-/
module

public import Spec.time.NowLoc
public import Perennial.Spec.time.runtimeNow

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Now.wp_proofLoc
    (wp_runtimeNow : _root_.Perennial.time.runtimeNow.spec (GF := GF) (hG := hG)) :
    time.Now.specLoc (GF := GF) (hG := hG) := by
  wp_start
  ihave #Hi := _root_.Perennial.time.isInit_access $$ Hpkg
  icases Hi with ⟨⟨%sn, #Hsn⟩, ⟨%loc, #Hloc⟩, -⟩
  wp_auto
  wp_apply wp_runtimeNow as %sec %nsec %mono -
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals (iapply HΦ; iexists loc; iframe #; ipureintro; rfl)

end proof

end EtcdGrove
end Perennial
