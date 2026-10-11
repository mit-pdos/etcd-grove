module
public import Spec.go_etcd_io.bbolt.newBucket

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem newBucket.wp_proof : newBucket.spec (GF := GF) (hG := hG) := by
  intro txl t dq
  wp_start as Ht
  wp_auto
  cases Hif : t.writable'
  rotate_left
  · try wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %bm Hbm
    try wp_auto
    wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %nm Hnm
    try wp_auto
    ispecialize HΦ $$ %bm %nm
    simp only [↓reduceIte]
    simp only [newBucketOf, defaultFillPercent]
    iapply HΦ; iframe
  · try wp_auto
    ispecialize HΦ $$ %map.nil %map.nil
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [newBucketOf, defaultFillPercent, map.nil]
    iapply HΦ; iframe; ipureintro; trivial

end proof

end bbolt
end EtcdGrove
end Perennial
