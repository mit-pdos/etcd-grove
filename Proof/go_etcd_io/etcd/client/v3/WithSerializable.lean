/-
Proof of `Spec/WithSerializable.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithSerializable

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem WithSerializable.wp_proof : WithSerializable.spec (GF := GF) (hG := hG) := by
  wp_start
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold optSpec
  imodintro
  iintro %opp %op %o
  wp_start as ⟨Hop, #Hat⟩
  wp_auto
  iapply HΦ
  iframe
  unfold opFullAt opAt OpFields
  icases Hat with ⟨⟨%Hf, #He⟩, #Hk, %Ht⟩
  simp only [withSerializableM]
  iframe #
  isplitl [] <;> ipureintro <;> simp_all

end proof

end EtcdGrove
end Perennial
