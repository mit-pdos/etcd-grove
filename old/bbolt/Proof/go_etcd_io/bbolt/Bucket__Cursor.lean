module
public import Spec.go_etcd_io.bbolt.Bucket__Cursor
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

theorem Bucket.Cursor.wp_proof (hInc : TxStats.IncCursorCount.spec (GF := GF) (hG := hG)) :
    Bucket.Cursor.spec (GF := GF) (hG := hG) := by
  intro bl V q
  wp_start as ⟨Hctx, Hpgs, Hst⟩
  unfold bktCtx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, Hbk, Hib, Ht, Hdata, Hps, %Hcx⟩
  have Hbtx : bv.tx' = V.tx := Hcx.2.2.2.2.2.2.2.1
  unfold txStats
  icases Hst with ⟨%s, Hst⟩
  wp_auto
  rw [Hbtx]
  wp_apply hInc $$ [Hst] as %s' ⟨-, Hst⟩
  · iframe
  try wp_auto
  wp_apply wp_slice_make2 (V := elemRef) (W64 0) $$ [] as %sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  try wp_auto
  wp_alloc cl as Hcl
  try wp_auto
  iapply HΦ
  isplitl [Hcl Hsl Hcap Hbk Hib Ht Hdata Hps Hpgs]
  · unfold curI bktCtx
    iexists { bucket' := bl, stack' := sl }
    simp only [List.replicate_zero] at *
    isplitr
    · ipureintro; trivial
    iframe
    rw [Hbtx]
    iframe
    ipureintro
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, -, a9, a10, a11⟩ := Hcx
    exact ⟨a1, a2, a3, a4, a5, a6, a7, rfl, a9, a10, a11⟩
  · iexists s'; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
