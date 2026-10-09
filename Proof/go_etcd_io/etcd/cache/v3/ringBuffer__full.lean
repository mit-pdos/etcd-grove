/-
Proof of `Spec/ringBuffer__full.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__full

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

theorem ringBuffer.full.wp_proof : ringBuffer.full.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items
  wp_start as H
  iNamed H
  wp_auto
  have Heq : decide (rb.size' = rb.buffer'.len) = decide (items.length = cap) := by
    have h1 := Hok.size; have h2 := Hok.len
    rw [decide_eq_decide]
    constructor
    · intro h; rw [h] at h1; omega
    · intro h; apply BitVec.toInt_inj.1; simp only [sint.Z] at h1 h2; omega
  rw [Heq]
  iapply HΦ
  iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf

end proof

end EtcdGrove
end Perennial
