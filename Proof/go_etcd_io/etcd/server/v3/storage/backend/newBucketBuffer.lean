/-
Proof of `Spec/.../backend/newBucketBuffer.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBucketBuffer
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RangeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.newBucketBuffer.wp_proof : backend.newBucketBuffer.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply (wp_slice_make2 (V := kv) (W64 512)) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  wp_alloc bb as Hbb
  wp_auto
  ihave #Hro := slotsRO_replicate_zero (GF := GF) 512
  ihave #Hin := entsIn_nil_r (GF := GF) (List.replicate 512 (zero_val kv))
  iapply HΦ
  iunfold ownBB
  iexists { buf := sl, kvs := List.replicate 512 (zero_val kv) }
  iunfold bbAt
  simp only [List.length_nil]
  iframe # ∗
  ipureintro; unfold bbOk; simp only [List.length_replicate, List.length_nil]; decide

end proof

end EtcdGrove
end Perennial
