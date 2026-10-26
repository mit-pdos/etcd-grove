/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/InRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.InRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem InRange.wp_proof : InRange.spec (GF := GF) (hG := hG) := by
  intro k
  wp_start
  simp only [github_com.mit_pdos.etcd_grove.examples.authkv.lo,
    github_com.mit_pdos.etcd_grove.examples.authkv.hi]
  wp_auto
  by_cases h1 : go.GoStringLe lo k
  · simp only [h1, decide_true]
    wp_auto
    by_cases h2 : go.GoStringLt k hi <;> simp [inRangeK, h1, h2] <;> wp_end
  · simp only [h1, decide_false]
    wp_auto
    simp [inRangeK, h1]
    wp_end

end proof

end authkv
end EtcdGrove
end Perennial
