/-
The proof of `Spec/hash/crc32/archAvailableCastagnoli.lean`, over the trusted model.
-/
module

public import Spec.hash.crc32.archAvailableCastagnoli

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

theorem hash.crc32.archAvailableCastagnoli.wp_proof :
    hash.crc32.archAvailableCastagnoli.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_apply wp_ArbitraryInt as %x -
  try wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
