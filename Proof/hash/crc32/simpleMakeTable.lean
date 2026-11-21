/-
The proof of `Spec/hash/crc32/simpleMakeTable.lean`, over `simplePopulateTable`'s.
-/
module

public import Spec.hash.crc32.simpleMakeTable
public import Spec.hash.crc32.simplePopulateTable

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

theorem hash.crc32.simpleMakeTable.wp_proof
    (hpop : hash.crc32.simplePopulateTable.spec (GF := GF) (hG := hG)) :
    hash.crc32.simpleMakeTable.spec (GF := GF) (hG := hG) := by
  intro poly
  wp_start as -
  wp_auto
  wp_apply hpop $$ [«$r0»] as Ht
  · iexact «$r0»
  (try wp_auto)
  iapply HΦ
  iexact Ht

end proof

end EtcdGrove
end Perennial
