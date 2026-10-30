module
public import Proof.go_etcd_io.bbolt.Init
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_w
public import Spec.go_etcd_io.bbolt.TxStats__IncCursorCount

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

theorem Bucket.Cursor.wp_wproof (hInc : TxStats.IncCursorCount.spec (GF := GF) (hG := hG)) :
    Bucket.Cursor.wspec (GF := GF) (hG := hG) := by
  intro bl bv dqb st
  wp_start as ⟨Hb, Hst⟩
  wp_auto
  wp_apply hInc $$ [Hst] as %s' ⟨%Hs', Hst⟩
  · iframe
  try wp_auto
  wp_apply wp_slice_make2 (V := elemRef) (W64 0) $$ [] as %sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  try wp_auto
  wp_alloc cl as Hcl
  try wp_auto
  simp only [List.replicate_zero] at *
  iapply HΦ
  rw [← Hs']
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
