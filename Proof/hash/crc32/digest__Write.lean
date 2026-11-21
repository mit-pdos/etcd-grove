/-
The proof of `Spec/hash/crc32/digest__Write.lean`, over `update`'s.
-/
module

public import Spec.hash.crc32.digest__Write

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

theorem hash.crc32.digest.Write.wp_proof (hupd : hash.crc32.update.spec (GF := GF) (hG := hG)) :
    hash.crc32.digest.Write.spec (GF := GF) (hG := hG) := by
  intro d c tab s bs dq
  wp_start as ⟨Hd, #Ht, Hs⟩
  wp_auto
  wp_apply hupd $$ [Hs] as Hs
  · iframe #; iexact Hs
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
