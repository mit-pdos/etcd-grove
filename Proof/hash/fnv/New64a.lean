/-
The proof of `Spec/hash/fnv/New64a.lean`: the translated body.
-/
module

public import Spec.hash.fnv.New64a

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

theorem hash.fnv.New64a.wp_proof : hash.fnv.New64a.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  unfold hash.fnv.fnv64aOffset
  iexact s

end proof

end EtcdGrove
end Perennial
