/-
The proof of `Spec/hash/crc32/MakeTable.lean` over the translated switch (`crc32.go:122-133`): the
`Castagnoli` case calls `castagnoliInitOnce` (the package's fact: it returns with `castagnoliTable`
set up, `castagnoliReady`) and returns `castagnoliTable`.
-/
module

public import Spec.hash.crc32.MakeTable

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

theorem hash.crc32.MakeTable.wp_proof : hash.crc32.MakeTable.spec (GF := GF) (hG := hG) := by
  wp_start as -
  ihave #Hf : (hash.crc32.crc32Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold hash.crc32.crc32Init at Hf
  icases Hf with ⟨-, ⟨%g, #Hg, #Hgs⟩, -⟩
  wp_auto
  wp_apply Hgs as Hready
  iunfold hash.crc32.castagnoliReady at Hready
  icases Hready with ⟨%t, #Hct, #Htt⟩
  try wp_auto
  iapply HΦ
  iexact Htt

end proof

end EtcdGrove
end Perennial
