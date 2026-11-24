/-
The proof of `Spec/hash/crc32/archUpdateCastagnoli.lean`, over the trusted model: `simpleUpdate` over
a fresh `simpleMakeTable(Castagnoli)`.
-/
module

public import Spec.hash.crc32.archUpdateCastagnoli
public import Spec.hash.crc32.simpleMakeTable
public import Spec.hash.crc32.simpleUpdate

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

theorem hash.crc32.archUpdateCastagnoli.wp_proof
    (hmk : hash.crc32.simpleMakeTable.spec (GF := GF) (hG := hG))
    (hupd : hash.crc32.simpleUpdate.spec (GF := GF) (hG := hG)) :
    hash.crc32.archUpdateCastagnoli.spec (GF := GF) (hG := hG) := by
  -- the Go model: `return simpleUpdate(crc, simpleMakeTable(Castagnoli), p)`
  intro c s bs dq
  wp_start as Hs
  try wp_auto
  wp_apply hmk as %t Ht
  try wp_auto
  wp_apply hupd $$ [Ht Hs] as ⟨-, Hs⟩
  · iframe
  rw [show hash.crc32.crcUpdate (array.mk 256 (hash.crc32.crcTableOf hash.crc32.castagnoliPoly)).arr c bs =
    hash.crc32.crc32c c bs from rfl]
  iapply HΦ
  iexact Hs

end proof

end EtcdGrove
end Perennial
