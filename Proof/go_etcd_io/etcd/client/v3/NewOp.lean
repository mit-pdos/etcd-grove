/-
Proof of `Spec/NewOp.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewOp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem NewOp.wp_proof : NewOp.spec (GF := GF) (hG := hG) := by
  wp_start
  iapply wp_fupd
  wp_apply wp_string_to_bytes _ as %ksl ⟨Hks, -⟩
  ipersist Hks
  wp_alloc opp as Hop
  wp_auto
  imodintro
  iapply HΦ
  iframe Hop
  unfold opFullAt opAt OpFields
  dsimp only [OpFull.newOp, OpModel.zero]
  isplitl []
  · isplitl []
    · ipureintro; simp
    · iapply ownSlice_nil
  isplitl []
  · iexact Hks
  ipureintro; simp

end proof

end EtcdGrove
end Perennial
