/-
The proof of `Spec/hash/fnv/sum64a__Sum64.lean`: the translated body.
-/
module

public import Spec.hash.fnv.sum64a__Sum64

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
variable [hash.fnv.Assumptions]

theorem hash.fnv.sum64a.Sum64.wp_proof : hash.fnv.sum64a.Sum64.spec (GF := GF) (hG := hG) := by
  intro l h dq
  wp_start as Hl
  wp_auto
  iapply HΦ
  iexact Hl

end proof

end EtcdGrove
end Perennial
