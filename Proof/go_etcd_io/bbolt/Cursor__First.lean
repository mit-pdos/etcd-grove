module
public import Spec.go_etcd_io.bbolt.Cursor__First
public import Proof.go_etcd_io.bbolt.CursorLemmas
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.Cursor__first

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

set_option maxHeartbeats 400000 in
theorem Cursor.First.wp_proof
    (hAssert : _root_.Perennial.EtcdGrove.bbolt.Assert.spec (GF := GF) (hG := hG))
    (hfirst : Cursor.first.spec (GF := GF) (hG := hG)) :
    Cursor.First.spec (GF := GF) (hG := hG) := by
  intro cl bl V q es Hok Hwf
  wp_start as Hc
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  unfold curI
  icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  unfold bktCtx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, %d1, %d2, %d3, %d4, Hbk, Hib, Ht, Hdata, Hps, %Hcx⟩
  wp_auto
  rw [Hb]
  try wp_auto
  have Hdn : t.db' ≠ null := by rw [Hcx.2.2.2.1]; exact Hcx.2.2.2.2.2.2
  rw [decide_eq_false Hdn]
  try wp_auto
  wp_apply hAssert
  ihave Hc : curI cl bl V q es $$ [Hcl Hs Hcap Hbk Hib Ht Hdata Hps Hpgs]
  · unfold curI bktCtx; iexists cv; iframe; ipureintro; exact ⟨Hb, Hcx⟩
  try wp_auto
  wp_apply hfirst cl bl V q es Hok Hwf $$ [Hc] as %es' %k %v %f ⟨%Hf, Hc⟩
  · iframe
  try wp_auto
  ispecialize HΦ $$ %es' %k %v %f
  by_cases Hfl : f &&& W32 1 = W32 0
  · rw [decide_eq_true Hfl]
    try wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; exact ⟨Hf.1, Hf.2.2⟩
    unfold curI bktCtx
    iexact Hc
  · rw [decide_eq_false Hfl]
    try wp_auto
    have Hv : kvVal v f = slice.nil := by unfold kvVal; rw [ite_eq_right_of_eq_false _ _ (eq_false Hfl)]
    rw [Hv]
    iapply HΦ
    isplitl []
    · ipureintro; exact ⟨Hf.1, Hf.2.2⟩
    unfold curI bktCtx
    iexact Hc

end proof

end bbolt
end EtcdGrove
end Perennial
