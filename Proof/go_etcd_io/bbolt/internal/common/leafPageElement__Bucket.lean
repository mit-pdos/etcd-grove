module
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Bucket
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem leafPageElement.Bucket.wp_proof
    (hE : leafPageElement.IsBucketEntry.spec (GF := GF) (hG := hG))
    (hV : leafPageElement.Value.spec (GF := GF) (hG := hG))
    (hLB : LoadBucket.spec (GF := GF) (hG := hG)) :
    leafPageElement.Bucket.spec (GF := GF) (hG := hG) := by
  intro l v dq Hc Hend Hpos
  wp_start as Hl
  wp_auto
  wp_apply hE $$ [$Hl] as Hl
  by_cases Hb : v.flags' &&& W32 1 = W32 0
  · rw [decide_eq_true Hb]
    try wp_auto
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using Hb))]
    iapply HΦ; iframe
  · rw [decide_eq_false Hb]
    try wp_auto
    wp_apply hV l v dq Hc Hend $$ [$Hl] as Hl
    wp_apply hLB _ (by have := Hpos Hb; simp only; word)
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hb)]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
