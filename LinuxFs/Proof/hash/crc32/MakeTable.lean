/-
The proof of `LinuxFs/Spec/hash/crc32/MakeTable.lean`: the trusted model's allocation, frozen.
-/
module

public import LinuxFs.Spec.hash.crc32.MakeTable

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
variable [hash.crc32.Assumptions]

theorem hash.crc32.MakeTable.wp_proof : hash.crc32.MakeTable.spec (GF := GF) (hG := hG) := by
  wp_start as -
  iapply wp_fupd
  wp_apply IntoValTyped.wp_alloc (t := go.ArrayType 256 go.uint32) hash.crc32.castagnoliTableArr
    as %l Hl
  imod (typedPointsto_dfractional (GF := GF) _ hash.crc32.castagnoliTableArr).dfractional_persist _ $$ Hl
    with #Hl
  imodintro
  iapply HΦ
  iexact Hl

end proof

end EtcdGrove
end Perennial
