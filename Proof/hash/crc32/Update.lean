/-
The proof of `Spec/hash/crc32/Update.lean`: `Update` is `update(crc, tab, p, true)` (`crc32.go:217-221`).
-/
module

public import Spec.hash.crc32.update
public import Spec.hash.crc32.Update

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

theorem hash.crc32.Update.wp_proof (hupd : hash.crc32.update.spec (GF := GF) (hG := hG)) :
    hash.crc32.Update.spec (GF := GF) (hG := hG) := by
  intro c tab s bs dq
  wp_start as ⟨#Ht, Hs⟩
  wp_auto
  wp_apply hupd $$ [Hs] as Hs
  · iframe #; iexact Hs
  iapply HΦ
  iexact Hs

end proof

end EtcdGrove
end Perennial
