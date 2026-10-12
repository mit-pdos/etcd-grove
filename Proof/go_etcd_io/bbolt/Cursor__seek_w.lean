module
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__search_w
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_w
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage

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

theorem Cursor.seek.wp_wproof
    (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hsearch : Cursor.search.wspec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue.wspec (GF := GF) (hG := hG)) :
    Cursor.seek.wspec (GF := GF) (hG := hG) := by
  intro cl cv es W hwm bl B txl pmap pm dqp key kb dk Hb HOK
  wp_start as ⟨Hcl, Hs, Hcap, Hctx, Hk⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
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
  unfold wctx
  icases Hctx with ⟨Hbk, Hv, Hpf, Hpm, Hdb⟩
  isimp only [bktOwn] at Hbk
  icases Hbk with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  wp_method_call
  try wp_auto
  wp_apply hRoot $$ [Hib] as Hib
  · iframe
  ihave Hctx : wctx W bl B txl pmap pm dqp $$ [Hbv Hib Hnm Hbm Hpo Hns Hv Hpf Hpm Hdb]
  · unfold wctx bktOwn; iframe
  try wp_auto
  have Hroot := posOK_root W hwm bl B HOK.2.1
  wp_apply hsearch cl { bucket' := bl, stack' := slice.slice cv.stack' elemRef (W64 0) (W64 0) } [] W hwm bl B
      txl pmap pm dqp B.ib.root' key kb dk rfl HOK Hroot $$ [Hcl Hs Hcap Hctx Hk]
    as %cv' %path ⟨%Hsp, Hcl, Hs, Hcap, Hctx, Hk⟩
  · iframe
  obtain ⟨Hb', Hpath⟩ := Hsp
  obtain ⟨pid', r, ks, Hlast, Hra, Hpos', Hkids, Hi0⟩ :=
    wpath_last W hwm bl B HOK.2.1 path B.ib.root' Hpath Hroot
  simp only [List.nil_append]
  try wp_auto
  rcases Hra with ⟨l, Hres, Hn, Hp⟩ | ⟨Hres, Hn, pg, Hpa⟩
  · -- a leaf node
    unfold kidsAt at Hkids
    rw [Hres] at Hkids
    obtain ⟨nrec, Hrec, Hrk⟩ := Option.map_eq_some_iff.1 Hkids
    simp only [Prod.mk.injEq] at Hrk
    have HN := HOK.2.1.2.2.2.2.2.2.2.1 l nrec Hrec
    obtain ⟨-, Hilen, -, -, Hlive, -⟩ := id HN
    have Hnn : r.node' ≠ null := by
      rw [Hn]
      unfold resolve at Hres
      split at Hres
      · split at Hres
        · cases Hres
        · cases Hres; assumption
      · exact (HOK.2.1.2.2.2.2.1 _ _ Hres).1
    unfold wctx
    icases Hctx with ⟨Hbk, Hv, Hpf, Hpm, Hdb⟩
    icases bktOwn_node_acc W bl B l nrec Hrec $$ Hbk with ⟨Hnd, Hback⟩
    isimp only [nodeOwn] at Hnd
    icases Hnd with ⟨Hn0, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
    wp_apply hkv cl cv' (DFrac.own 1) path (DFrac.own 1) r (DFrac.own 1) [] nrec.nv (DFrac.own 1) nrec.ins
      (DFrac.own 1) Hlast (fun h => absurd h Hnn) (fun _ => Hi0) $$ [Hcl Hs Hn0 Hins] as ⟨Hcl, Hs, Hres'⟩
    · simp only [Hnn, ↓reduceIte]; rw [Hn]; iframe
    simp only [Hnn, ↓reduceIte]
    icases Hres' with ⟨Hn0, Hins⟩
    rw [Hn]
    ihave Hbk := Hback $$ %nrec [Hn0 Hins Hicap Hents Hch Hchcap Hkey]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B l nrec Hrec]
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro
      refine ⟨Hb', Hpath, ?_⟩
      unfold kvResW; rw [if_neg Hnn]
      exact nodeKV_keySrc W B l nrec _ Hrec Hlive Hilen
    iframe
  · -- a leaf page
    unfold kidsAt at Hkids
    rw [Hres, Hpa] at Hkids
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at Hkids
    have Hinl : B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale := by
      intro h0
      rcases Hpos'.2 with ⟨l, r, h1, -⟩ | ⟨-, ⟨-, -, h2, h3, -⟩ | ⟨h4, -⟩⟩
      · rw [Hres] at h1; cases h1
      · exact ⟨h2, h3⟩
      · exact absurd h0 h4
    have Hlw : 16 ≤ pg.length ∧ leafWF pg pg.length := by
      by_cases hr : B.ib.root' = W64 0
      · rcases Hpos'.2 with ⟨l, r, h1, -⟩ | ⟨-, ⟨-, h0, -, -, hg⟩ | ⟨h4, -⟩⟩
        · rw [Hres] at h1; cases h1
        · unfold wpageAt at Hpa; rw [if_pos hr, if_pos h0] at Hpa
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj Hpa)
          exact ⟨hg.2.2.2.1, hg.2.2.1⟩
        · exact absurd hr h4
      · obtain ⟨pg', hpg, hpa', hwf, -⟩ := posOK_page W hwm B pid' hr Hres Hpos'
        rw [Hpa] at hpa'
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hpa')
        obtain ⟨hl, -, -, hk⟩ := treeWF_page _ _ _ _ hwf hpg
        rcases hk with ⟨-, hw, -⟩ | ⟨hfl, -, -⟩
        · exact ⟨hl, hw⟩
        · rw [hfl] at Hkids; exact absurd Hkids.1 (by unfold branchPageFlag leafPageFlag; decide)
    have Hne : pg ≠ [] := by intro h; rw [h] at Hlw; simp at Hlw
    unfold wctx
    icases Hctx with ⟨Hbk, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    isimp only [bktOwn] at Hbk
    icases Hbk with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    icases wpageAt_acc W B pid' r.page' pg HOK.1.1 Hpa Hinl Hne $$ [Hpv Hpo] with ⟨%dq, %Hc, Hpg, Hpgback⟩
    · iframe
    wp_apply hkv cl cv' (DFrac.own 1) path (DFrac.own 1) r dq pg (zero_val node) (DFrac.own 1) []
      (DFrac.own 1) Hlast (fun _ => ⟨Hc, Hlw.1, Hkids.1, Hlw.2, Or.inl Hi0⟩) (fun h => absurd Hn h)
      $$ [Hcl Hs Hpg] as ⟨Hcl, Hs, Hpg⟩
    · simp only [Hn, ↓reduceIte]; iframe
    simp only [Hn, ↓reduceIte]
    ihave Hpg := Hpgback $$ Hpg
    icases Hpg with ⟨Hpv, Hpo⟩
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro
      refine ⟨Hb', Hpath, ?_⟩
      unfold kvResW; rw [if_pos Hn]
      exact kvResult_keySrc W B pid' r.page' pg _ Hpa Hinl Hlw.1 Hlw.2
    iframe
    unfold wView bktOwn; iframe; iframe #; ipureintro; exact Hlgv

end proof

end bbolt
end EtcdGrove
end Perennial
