/- Lean-first (no Rocq counterpart). The proof of `pageAt`: `&b[off]` is `off` bytes past the slice's start. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pageAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem pageAt.wp_proof : pageAt.spec (GF := GF) (hG := hG) := by
  intro buf off
  wp_start as %H
  wp_auto
  simp only [show 0 ≤ sint.Z off ∧ sint.Z off < sint.Z buf.len from H.2, and_self, ite_true]
  wp_auto
  rw [sliceIndexRef_byte _ _ H.1 H.2.1]
  iapply HΦ
  itrivial

end proof

end bboltfs
end EtcdGrove
end Perennial
