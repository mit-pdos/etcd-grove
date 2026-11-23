/-
The proof of `Spec/hash/crc32/New.lean`.
-/
module

public import Spec.hash.crc32.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

theorem hash.crc32.New.wp_proof : hash.crc32.New.spec (GF := GF) (hG := hG) := by
  intro tab
  wp_start as #Ht
  ihave #Hf : (hash.crc32.crc32Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold hash.crc32.crc32Init at Hf
  icases Hf with ⟨⟨%t, #Hg, #Hi⟩, -, -⟩
  ihave %hne : ⌜tab ≠ t⌝ $$ []
  · iintro %h
    subst h
    icombine Ht Hi gives %Heq
    exact absurd Heq.symm hash.crc32.ieeeTableArr_ne
  wp_auto
  rw [decide_eq_false hne]
  wp_auto
  wp_alloc dp as Hdp
  wp_auto
  iapply HΦ
  iexact Hdp

end proof

end EtcdGrove
end Perennial
