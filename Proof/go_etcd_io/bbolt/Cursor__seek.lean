module
public import Spec.go_etcd_io.bbolt.Cursor__seek
public import Proof.go_etcd_io.bbolt.CursorLemmas
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Spec.go_etcd_io.bbolt.Cursor__search
public import Spec.go_etcd_io.bbolt.Cursor__keyValue

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
theorem Cursor.seek.wp_proof
    (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hsearch : Cursor.search.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue.spec (GF := GF) (hG := hG)) :
    Cursor.seek.spec (GF := GF) (hG := hG) := by
  intro cl bl V q es key kb dk Hok Hwf
  wp_start as ⟨Hc, Hk⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  unfold curI
  icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  ihave %Hwfs := ownSlice_wf _ _ _ $$ Hs
  wp_auto
  have h00 : sint.Z (W64 0) = 0 := rfl
  have hn0 : sint.nat (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
  icases ownSlice_slice_with_cap (W64 0) (W64 0) cv.stack' _ ⟨by omega, by omega, by omega⟩ $$ [Hs Hcap]
    with ⟨-, Hs, Hcap⟩
  · iframe
  rw [hn0, show subslice 0 0 es = ([] : List elemRef) by simp [subslice]]
  try wp_auto
  rw [Hb]
  unfold bktCtx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, %d1, %d2, %d3, %d4, Hbk, Hib, Ht, Hdata, Hps, %Hcx⟩
  wp_method_call
  try wp_auto
  wp_apply hRoot $$ [Hib] as Hib
  · iframe
  rw [Hcx.1]
  ihave Hctx : bktCtx bl V $$ [Hbk Hib Ht Hdata Hps]
  · unfold bktCtx; iframe; ipureintro; exact Hcx
  try wp_auto
  wp_apply hsearch cl { cv with stack' := slice.slice cv.stack' elemRef (W64 0) (W64 0) } [] V q V.root
      key kb dk Hok Hwf $$ [Hcl Hs Hcap Hctx Hpgs Hk]
    as %cv' %path %pg %idx ⟨%Hsp, Hcl, Hs, Hcap, Hctx, Hpgs, Hk⟩
  · simp only [Hb]
    iframe
  obtain ⟨Hb', Hsok, Hslf, -, Hseek⟩ := Hsp
  obtain ⟨pid', r, Hcp, Hfl, Hri⟩ := stackOK_curPath V Hok path V.root pg idx Hwf Hsok Hslf Hseek.1
  have Hlt : leafTop V path r pg := ⟨pid', Hcp, Hfl⟩
  obtain ⟨pid3, pre3, Hes3, -, -, Hpa3, Hn3, Hlen3, Hfl3, Hlw3, Hli3, Hc3⟩ :=
    leafTop_facts V path r pg Hok Hlt
  icases bktPages_acc V q pid3 _ pg Hok Hpa3 $$ Hpgs with ⟨Hpg, Hpgsback⟩
  simp only [List.nil_append]
  try wp_auto
  wp_apply hkv cl cv' (DFrac.own 1) path (DFrac.own 1) r (DFrac.own q) pg (by rw [Hes3]; simp)
    Hn3 Hc3 Hlen3 Hfl3 Hlw3 (Hli3.2.imp_right (·.2)) $$ [Hcl Hs Hpg] as ⟨Hcl, Hs, Hpg⟩
  · iframe
  ispecialize Hpgsback $$ Hpg
  try wp_auto
  simp only [Hb] at Hb' ⊢
  iapply HΦ
  isplitl []
  · ipureintro; exact ⟨Hlt, Hri ▸ Hseek⟩
  unfold bktCtx
  iframe
  ipureintro; exact Hb'

end proof

end bbolt
end EtcdGrove
end Perennial
