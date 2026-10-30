module
public import Spec.go_etcd_io.bbolt.node__rebalance_s
public import Spec.go_etcd_io.bbolt.node__free_s
public import Spec.go_etcd_io.bbolt.node__nextSibling_s
public import Spec.go_etcd_io.bbolt.node__prevSibling_s
public import Spec.go_etcd_io.bbolt.node__childAt
public import Spec.go_etcd_io.bbolt.node__childIndex
public import Spec.go_etcd_io.bbolt.node__numChildren
public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.node__minKeys
public import Spec.go_etcd_io.bbolt.node__del
public import Spec.go_etcd_io.bbolt.node__removeChild
public import Spec.go_etcd_io.bbolt.TxStats__IncRebalance
public import Spec.go_etcd_io.bbolt.Bucket__node
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Proof.go_etcd_io.bbolt.RebalanceWP
public import Proof.go_etcd_io.bbolt.RebalanceDB
public import Proof.go_etcd_io.bbolt.FloatConv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [float_sem : go.FloatConvSemantics]

/-- `node.rebalance.sspec`, as an Iris proposition (for the recursion). -/
def rebalIw : IProp GF :=
  iprop(∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (hwm : Nat) (txl : Loc)
    (txid : w64) (ρ : DBState) (bl : Loc) (B : BRec) (st : TxStats) (pmap : GoMap) (mp : Loc)
    (mv : Meta) (F : GMap Nat (List w8)) (nl : Loc) (r : NRec) (dfc : Option Loc),
  ⌜I.FreeSpec ∧ viewOK W ∧ rblB W hwm bl B dfc ∧ B.bv.tx' = txl ∧ B.ns !! nl = some r ∧
    (dfc = none ∨ (dfc = some nl ∧ r.nv.unbalanced' = true)) ∧ mv.txid' = txid ∧
    freedOK W ρ.fl txid F⌝ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktOwn W bl B ∗ wView W ∗
      rblTx txl st pmap mp mv W.dbl ∗ dbWR I γd W txl txid ρ ∗ bktToks γ W B ∗ pgToks γ F }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (B' : BRec) (st' : TxStats) (ρ' : DBState) (F' : GMap Nat (List w8)),
      bktOwn W bl B' ∗ wView W ∗ rblTx txl st' pmap mp mv W.dbl ∗ dbWR I γd W txl txid ρ' ∗
      bktToks γ W B' ∗ pgToks γ F' ∗
      ⌜rblB W hwm bl B' none ∧ rblStep B B' nl ∧ freedOK W ρ'.fl txid F' ∧
        (∃ fl, ρ' = { ρ with fl := fl }) ∧ ∀ k v, entryIn W B k v → entryIn W B' k v⌝ }})

set_option maxHeartbeats 3000000 in
theorem rebal_loeb (hInc : TxStats.IncRebalance.spec (GF := GF) (hG := hG))
    (hsize : node.size.spec (GF := GF) (hG := hG))
    (hmin : node.minKeys.spec (GF := GF) (hG := hG))
    (hPgid : Inode.Pgid.spec (GF := GF) (hG := hG))
    (hnode : Bucket.node.spec (GF := GF) (hG := hG))
    (hfree : node.free.sspec (GF := GF) (hG := hG))
    (hnc : node.numChildren.spec (GF := GF) (hG := hG))
    (hdel : node.del.spec (GF := GF) (hG := hG))
    (hrc : node.removeChild.spec (GF := GF) (hG := hG))
    (hA : Assert.spec (GF := GF) (hG := hG))
    (hci : node.childIndex.spec (GF := GF) (hG := hG))
    (hnext : node.nextSibling.sspec (GF := GF) (hG := hG))
    (hprev : node.prevSibling.sspec (GF := GF) (hG := hG)) :
    ⊢ rebalIw (GF := GF) := by
  iloeb as IH
  unfold rebalIw
  iintro %I %γd %γ %W %hwm %txl %txid %ρ %bl %B %st %pmap %mp %mv %F %nl %r %dfc %Hpre
  obtain ⟨hFree, HvOK, HB, Htx, Hr, Hdfc, Hmtx, HF⟩ := Hpre
  wp_start as ⟨Hb, Hv, Htxr, Hdbw, Htk, HFt⟩
  unfold bktOwn
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
    (show Std.get? B.ns nl = some r from Hr)).1 $$ Hns with ⟨Hn, Hns⟩
  isimp only [nodeOwn] at Hn
  icases Hn with ⟨Hn, Hins, Hcap, Hents, Hch, Hchcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hins
  have Hdfc' : dfc = none ∨ dfc = some nl := by
    rcases Hdfc with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  wp_auto
  rcases Bool.eq_false_or_eq_true r.nv.unbalanced' with hu | hu0
  rotate_left
  · -- balanced: nothing
    rw [hu0]
    try wp_auto
    have hd : dfc = none := by
      rcases Hdfc with h | ⟨-, h⟩
      · exact h
      · rw [hu0] at h; cases h
    subst hd
    ihave Hns := (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
      (show Std.get? B.ns nl = some r from Hr)).2 $$ [Hns Hn Hins Hcap Hents Hch Hchcap Hkey]
    · iframe; unfold nodeOwn; iframe
    iapply HΦ
    iexists B, st, ρ, F
    iframe
    ipureintro
    refine ⟨HB, ⟨rfl, rfl, rfl, fun l r' hl hu' => ?_⟩, HF, ⟨ρ.fl, rfl⟩, fun _ _ h => h⟩
    have hne : l ≠ nl := by rintro rfl; rw [Hr] at hl; cases hl; rw [hu0] at hu'; cases hu'
    exact ⟨hne, r', hl, hu', rfl⟩
  rw [hu]
  try wp_auto
  have HNC := HB.1.2.2.2.2.2.2.2.1 nl r Hr
  have Hbl : r.nv.bucket' = bl := HNC.1
  rw [Hbl]
  try wp_auto
  rw [Htx]
  unfold rblTx
  icases Htxr with ⟨Hst, Hpf, Hpm, Hdbf, Hmf, Hmv⟩
  try wp_auto
  wp_apply hInc $$ [Hst] as %st1 ⟨%Hst1, Hst⟩
  · iframe
  try wp_auto
  rw [Htx]
  unfold wView
  icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
  try wp_auto
  wp_apply hsize nl _ (DFrac.own 1) r.ins (DFrac.own 1) $$ [Hn Hins] as ⟨Hn, Hins⟩
  · iframe
  try wp_auto
  by_cases hbig : sint.Z (BitVec.sdiv (go.float64ToInt64 (float64Mul (go.float64OfInt64 (W64 (W.ps : Int)))
      B.bv.FillPercent')) (W64 2)) < sint.Z (sizeFrom (W64 16) (W64 16) r.ins) ∧
      sint.Z (if r.nv.isLeaf' then W64 1 else W64 2) < sint.Z r.nv.inodes'.len
  · -- big enough: done
    rw [decide_eq_true hbig.1]
    try wp_auto
    wp_apply hmin $$ [Hn] as Hn
    · iframe
    try wp_auto
    rw [decide_eq_true hbig.2]
    try wp_auto
    have Hlen := HNC.2.1
    have h2 : r.nv.isLeaf' = false → 2 ≤ r.ws.length := by
      intro hl
      have := hbig.2; rw [hl] at this; simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [← Hlen, Hsl.1]; word
    have h1 : r.nv.isLeaf' = true → r.nv.parent' ≠ null → 0 < r.ws.length := by
      intro hl _
      have := hbig.2; rw [hl] at this; simp only [↓reduceIte] at this
      rw [← Hlen, Hsl.1]; word
    obtain ⟨Hd1, Hd2, Hd3⟩ := rbl_done W hwm bl B nl r dfc HB Hr Hdfc' h2 h1
    ihave Hns := ns_reins W B.ns nl (rblClear r) $$ [Hns Hn Hins Hcap Hents Hch Hchcap Hkey]
    · iframe; unfold nodeOwn; simp only [rblClear]; rw [Hbl]; iframe
    ihave Htk := (bktToks_set γ W B nl r (rblClear r) Hr (nrecEq_clear r)).2 $$ Htk
    iapply HΦ
    iexists rblStart B nl r, st1, ρ, F
    rw [pageOwn_congr W (rblStart B nl r) B rfl rfl rfl]
    iframe
    iframe #
    ipureintro
    exact ⟨Hlgv, Hd1, Hd2, HF, ⟨ρ.fl, rfl⟩, Hd3⟩
  · wp_join with [Hn n]
    · try wp_auto
      wp_apply hmin $$ [Hn] as Hn
      · iframe
      try wp_auto
      rw [decide_eq_false (fun h => hbig ⟨Hif, h⟩)]
      try wp_auto
      wp_join_done
    have Hlen := HNC.2.1
    wp_if_destruct
    · -- a root
      by_cases hcol : r.nv.isLeaf' = false ∧ r.nv.inodes'.len = W64 1
      · obtain ⟨hlf0, hlen1⟩ := hcol
        have Hlen1 : r.ws.length = 1 := by
          rw [← Hlen, Hsl.1, hlen1]; rfl
        obtain ⟨w0, Hw0l⟩ : ∃ w0, r.ws = [w0] := by
          match h : r.ws, Hlen1 with
          | [w0], _ => exact ⟨w0, rfl⟩
        have Hw0 : r.ws[0]? = some w0 := by rw [Hw0l]; rfl
        have Hil : 0 < r.ins.length := by rw [Hlen, Hlen1]; omega
        obtain ⟨it, Hit⟩ : ∃ it, r.ins[0]? = some it := ⟨_, List.getElem?_eq_getElem Hil⟩
        icases wOwn_at W r.ins r.ws 0 it w0 Hit Hw0 $$ Hents with ⟨%Hip, Hents⟩
        ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
        · iPkgInit
        rw [hlf0]
        try wp_auto
        rw [decide_eq_true hlen1]
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z r.nv.inodes'.len
          from ⟨by decide, by rw [hlen1]; decide⟩))]
        icases ownSlice_elem_acc (sint.Z (W64 0)) it r.nv.inodes' _ _ (by decide) Hit $$ Hins with ⟨Hit', Hsback⟩
        wp_apply hPgid $$ [$Hit'] as Hit'
        try wp_auto
        ihave Hins := Hsback $$ Hit'
        rw [show (sint.Z (W64 0)).toNat = 0 from rfl, list_set_lookup_self _ _ _ Hit]
        rw [Hip.2]
        have HB0 := rblB_start W hwm bl B nl r dfc HB Hr Hdfc'
        have Hr0 : (rblStart B nl r).ns !! nl = some (rblClear r) := by
          show (<[nl := rblClear r]> B.ns) !! nl = _; rw [GMap.lookup_insert]
        ihave Hns := ns_reins W B.ns nl (rblClear r) $$ [Hns Hn Hins Hcap Hents Hch Hchcap Hkey]
        · iframe; unfold nodeOwn; simp only [rblClear]; rw [Hbl, hlf0]; iframe
        ihave Hb : bktOwn W bl (rblStart B nl r) $$ [Hbv Hib Hnm Hbm Hpo Hns]
        · unfold bktOwn; rw [pageOwn_congr W (rblStart B nl r) B rfl rfl rfl]; iframe
        ihave Hv : wView W $$ [Hdata Hfli Hpv]
        · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
        ihave Htk : bktToks γ W (rblStart B nl r) $$ [Htk]
        · unfold rblStart; iapply (bktToks_set γ W B nl r (rblClear r) Hr (nrecEq_clear r)).2; iexact Htk
        obtain ⟨p0, pg0, src0, Hsrc0⟩ :=
          entry_srcOK W hwm bl (rblStart B nl r) HvOK HB0.1 nl (rblClear r) Hr0 hlf0 0 w0 Hw0
        wp_apply hnode W bl (rblStart B nl r) txl st1 pmap ∅ (DFrac.own 1) w0.pgid nl p0 pg0 src0 HvOK Htx
          (fun l hl => (HB0.1.2.2.2.2.1 _ _ hl).1)
          (fun hn => ⟨Hsrc0 hn, Or.inr (by rw [Hr0]; rfl)⟩)
          $$ [Hb Hv Hst Hpf Hpm Hdbf] as %lc %B1 %st2 ⟨Hb, Hv, Hst, Hpf, Hpm, Hdbf, %Hres⟩
        · iframe
        try wp_auto
        icases rbl_nodeRes γ W hwm bl (rblStart B nl r) (some nl) ∅ nl (rblClear r) 0 w0 p0 pg0 src0 lc B1
          st1 st2 HvOK HB0 Hr0 hlf0 Hw0 Hsrc0 Hres $$ Htk with ⟨Htk, %HR⟩
        obtain ⟨HB1, Hent1, hbv1, hib1, hbm1, hlc1, ⟨rc, hrc, hpc⟩, hun1, hkeep1⟩ := HR
        obtain ⟨rn, hrn, hrnws, hrnlf, hrnp, hrnu, hrnpg⟩ := hkeep1 nl (rblClear r) Hr0
        have hws1 : rn.ws = [w0] := by rw [hrnws]; exact Hw0l
        have hpn1 : rn.nv.parent' = null := by rw [hrnp]; exact Hif
        have hbr1 : rn.nv.isLeaf' = false := by rw [hrnlf]; exact hlf0
        obtain ⟨hp1, hlcn, hpg3, hnm1, hpg, hroot0, hkid, honly, -⟩ :=
          col_basic W hwm bl B1 nl rn w0 lc rc HB1.1 HB1.2.2.1 hrn hbr1 hpn1 hws1 hlc1 hrc
        isimp only [bktOwn] at Hb
        icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
          (show Std.get? B1.ns nl = some rn from hrn)).1 $$ Hns with ⟨Hn, Hns⟩
        have hrcd : Std.get? (Std.delete B1.ns nl) lc = some rc := by
          show (GMap.delete nl B1.ns) !! lc = _; rw [GMap.lookup_delete_ne _ (Ne.symm hlcn)]; exact hrc
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
          hrcd).1 $$ Hns with ⟨Hc, Hns⟩
        isimp only [nodeOwn] at Hn Hc
        icases Hn with ⟨Hn, Hins, Hcap, Hents, Hch, Hchcap, Hkey⟩
        icases Hc with ⟨Hc, Hcins, Hccap, Hcents, Hcch, Hcchcap, Hckey⟩
        ihave %Hcsl := ownSlice_len _ _ _ $$ Hcins
        try wp_auto
        ihave %Hcwf := ownSlice_wf _ _ _ $$ Hcins
        rw [← slice_slice_trivial (V := Inode) rc.nv.inodes', if_pos (show 0 ≤ sint.Z (W64 0) ∧
          sint.Z (W64 0) ≤ sint.Z rc.nv.inodes'.len ∧ sint.Z rc.nv.inodes'.len ≤ sint.Z rc.nv.inodes'.cap
          from ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hcwf.1, Hcwf.2⟩)]
        icases dbWR_view_keep I γd W txl txid ρ $$ Hdbw with ⟨Hdbw, %Hdv⟩
        have HNc := HB1.1.2.2.2.2.2.2.2.1 lc rc hrc
        have HNn := HB1.1.2.2.2.2.2.2.2.1 nl rn hrn
        have Hclen : rc.ins.length = rc.ws.length := HNc.2.1
        have Hlcn : lc ≠ null := (HB1.1.2.2.2.2.1 _ _ hlc1).1
        try wp_auto
        isimp only at Hn
        ihave IH2 : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
            "Hns" ∷ ([∗map] y ↦ ry ∈ Std.delete (Std.delete B1.ns nl) lc,
              nodeOwn (GF := GF) W y (repStep B1.nm lc nl rc.ws (sint.nat j) y ry)) ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rc.nv.inodes'.len⌝ : IProp GF) $$ [i Hns]
        · iexists W64 0
          simp only [named]
          rw [show sint.nat (W64 0) = 0 from rfl]
          simp only [repStep_zero]
          iframe
          ipureintro
          exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hcwf.1⟩
        wp_for IH2
        wp_if_destruct
        · have Hlt : sint.Z j < sint.Z rc.nv.inodes'.len := Hif
          have Hjn : sint.nat j < rc.ins.length := by rw [Hcsl.1]; word
          list_elem rc.ins (sint.nat j) as it
          obtain ⟨x, Hx⟩ : ∃ x, rc.ws[sint.nat j]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by rw [← Hclen]; exact Hjn)⟩
          rw [ite_cond_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rc.nv.inodes'.len
            from ⟨Hj.1, Hlt⟩))]
          wp_apply wp_load_slice_index rc.nv.inodes' (sint.Z j) rc.ins _ it Hj.1 $$ [Hcins] with Hcins
          · iframe; ipureintro; exact Hit_lookup
          try wp_auto
          icases wOwn_at W rc.ins rc.ws (sint.nat j) it x Hit_lookup Hx $$ Hcents with ⟨%Hipx, Hcents⟩
          rw [(HNn.1 : rn.nv.bucket' = bl)]
          try wp_auto
          wp_apply hPgid $$ [$inode] as inode
          try wp_auto
          rw [Hipx.2]
          wp_apply (wp_map_lookup2 (K := w64) (V := Loc) internal.common.Pgid.ty
            (go.GoType.PointerType node.ty) B1.bv.nodes' B1.nm x.pgid (DFrac.own 1)) $$ [Hnm] as Hnm
          · iframe
          try wp_auto
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          cases hcase : B1.nm !! x.pgid with
          | none =>
            simp only [Option.isSome_none, decide_false, Bool.false_eq_true]
            try wp_auto
            wp_for_post
            ihave Hns := rep_none W _ B1.nm lc nl rc.ws (sint.nat j) x Hx hcase $$ Hns
            iframe
            iexists j + W64 1
            rw [hj1]
            iframe
            ipureintro
            exact ⟨by word, by word⟩
          | some c =>
            have hxin : x ∈ rc.ws := List.mem_of_getElem? Hx
            have hrcb : rc.nv.isLeaf' = false := by
              rcases Bool.eq_false_or_eq_true rc.nv.isLeaf' with h | h
              · exact absurd (leaf_nokid W hwm bl B1 (some nl) HB1 Hdv.2 hroot0 lc rc hrc h x hxin)
                  (by rw [hcase]; nofun)
              · exact h
            obtain ⟨-, -, hkids⟩ := HNc.2.2.2.2.2.2.2.2.2.2.2.1 hrcb
            obtain ⟨rc', hrc', hpc'⟩ := (hkids x hxin).2.1 c hcase
            have hcn : c ≠ nl := by
              intro he; rw [he, hrn] at hrc'; cases hrc'; rw [hpn1] at hpc'; exact Hlcn hpc'.symm
            have hcl : c ≠ lc := by
              intro he; rw [he, hrc] at hrc'; cases hrc'; rw [hp1] at hpc'; exact hlcn hpc'.symm
            have hD : (Std.delete (Std.delete B1.ns nl) lc : GMap Loc NRec) !! c = some rc' := by
              show (GMap.delete lc (GMap.delete nl B1.ns)) !! c = _
              rw [GMap.lookup_delete_ne _ (Ne.symm hcl), GMap.lookup_delete_ne _ (Ne.symm hcn)]
              exact hrc'
            icases rep_hit W _ B1.nm lc nl rc.ws (sint.nat j) x Hx c hcase rc' hD $$ Hns
              with ⟨Hcc, Hback⟩
            isimp only [nodeOwn] at Hcc
            icases Hcc with ⟨Hcc, Hcc1, Hcc2, Hcc3, Hcc4, Hcc5, Hcc6⟩
            simp only [Option.isSome_some, decide_true, Option.getD_some]
            try wp_auto
            ihave Hns := Hback $$ [Hcc Hcc1 Hcc2 Hcc3 Hcc4 Hcc5 Hcc6]
            · rw [repStep_hit B1.nm lc nl rc.ws (sint.nat j) x Hx c hcase rc' hpc',
                ← repStep_set B1.nm lc nl rc.ws (sint.nat j) c rc']
              unfold nodeOwn; isimp only; iframe
            wp_for_post
            iframe
            iexists j + W64 1
            rw [hj1]
            iframe
            ipureintro
            exact ⟨by word, by word⟩
        have Hjeq : sint.nat j = rc.ws.length := by rw [← Hclen, Hcsl.1]; word
        rw [(HNn.1 : rn.nv.bucket' = bl)]
        try wp_auto
        wp_apply (wp_mapDelete (K := w64) (V := Loc) B1.bv.nodes' B1.nm rc.nv.pgid'
          internal.common.Pgid.ty (go.GoType.PointerType node.ty)) $$ [Hnm] as Hnm
        · iframe
        try wp_auto
        icases col_toks γ W hwm bl B1 nl rn w0 lc rc HB1.1 HB1.2.2.1 hrn hbr1 hpn1 hws1 hlc1 hrc
          rc.nv.inodes' $$ Htk with ⟨Htk, Hpt⟩
        ihave Htxr : rblTx txl st2 pmap mp mv W.dbl $$ [Hst Hpf Hpm Hdbf Hmf Hmv]
        · unfold rblTx; iframe
        wp_apply hfree I γd γ W hwm txl txid ρ bl B1.bv (DFrac.own 1) st2 pmap mp mv F lc
          ({ rc.nv with parent' := null } : node) hFree HvOK (by rw [hbv1]; exact Htx)
          HNc.1 Hmtx HF (fun _ => HNc.2.2.2.2.2.2.2.2.1 hroot0)
          $$ [Hc Hbv Hv Htxr Hdbw HFt Hpt] as ⟨%ρ1, %F1, Hc, Hbv, Hv, Htxr, Hdbw, HFt, %Hf1⟩
        · iframe
        try wp_auto
        obtain ⟨P1, P2, P3⟩ := col_post W hwm bl B B1 nl lc r rn rc w0 rc.nv.inodes' HB1 hbv1 hib1 hbm1
          hun1 hrn hbr1 hpn1 hws1 hlc1 hrc
        ihave Hns := col_own W B1 nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes') rc.ws
          (fun y ry hy _ _ hp => kid_pos W hwm bl B1 HB1.1 lc rc Hlcn hrc y ry hy hp)
          $$ [Hns Hn Hcins Hccap Hcents Hcch Hcchcap Hkey]
        · rw [Hjeq]; iframe; unfold nodeOwn colRoot; isimp only
          try rw [(HNn.1 : rn.nv.bucket' = bl)]
          iframe
        iapply HΦ
        iexists colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes'), st2, ρ1, F1
        isimp only [wView, rblTx] at Hv Htxr
        rw [pageOwn_congr W (colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes')) B1 rfl rfl rfl,
          show (colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes')).bv = B1.bv from rfl,
          show (colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes')).ib = B1.ib from rfl,
          show (colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes')).bm = B1.bm from rfl,
          show (colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes')).nm =
            GMap.delete rc.nv.pgid' B1.nm from rfl]
        iframe
        iframe #
        ipureintro
        obtain ⟨Hf1a, ⟨fl1, Hρ1⟩⟩ := Hf1
        refine ⟨P1, P2, Hf1a, ⟨fl1, Hρ1⟩, fun k v he => P3 k v (Hent1 k v ?_)⟩
        exact entryIn_sim W (bktSim_set B nl r (rblClear r) Hr (nrecEq_clear r)) k v he
      · have h2 : r.nv.isLeaf' = false → 2 ≤ r.ws.length := by
          intro hl
          have h0 := (HNC.2.2.2.2.2.2.2.2.2.2.2.1 hl).1
          have h1 : r.nv.inodes'.len ≠ W64 1 := fun h => hcol ⟨hl, h⟩
          rw [← Hlen, Hsl.1] at h0 ⊢
          have := Hsl.2
          have h1' : sint.nat r.nv.inodes'.len ≠ 1 := by intro h; apply h1; word
          omega
        have h1 : r.nv.isLeaf' = true → r.nv.parent' ≠ null → 0 < r.ws.length :=
          fun _ hp => absurd Hif hp
        obtain ⟨Hd1, Hd2, Hd3⟩ := rbl_done W hwm bl B nl r dfc HB Hr Hdfc' h2 h1
        rcases Bool.eq_false_or_eq_true r.nv.isLeaf' with hlf | hlf
        · rw [hlf]
          try wp_auto
          ihave Hns := ns_reins W B.ns nl (rblClear r) $$ [Hns Hn Hins Hcap Hents Hch Hchcap Hkey]
          · iframe; unfold nodeOwn; simp only [rblClear]; rw [Hbl, hlf]; iframe
          ihave Htk := (bktToks_set γ W B nl r (rblClear r) Hr (nrecEq_clear r)).2 $$ Htk
          iapply HΦ
          iexists rblStart B nl r, st1, ρ, F
          rw [pageOwn_congr W (rblStart B nl r) B rfl rfl rfl]
          iframe
          iframe #
          ipureintro
          exact ⟨Hlgv, Hd1, Hd2, HF, ⟨ρ.fl, rfl⟩, Hd3⟩
        · rw [hlf]
          try wp_auto
          rw [decide_eq_false (fun h => hcol ⟨hlf, by word⟩)]
          try wp_auto
          ihave Hns := ns_reins W B.ns nl (rblClear r) $$ [Hns Hn Hins Hcap Hents Hch Hchcap Hkey]
          · iframe; unfold nodeOwn; simp only [rblClear]; rw [Hbl, hlf]; iframe
          ihave Htk := (bktToks_set γ W B nl r (rblClear r) Hr (nrecEq_clear r)).2 $$ Htk
          iapply HΦ
          iexists rblStart B nl r, st1, ρ, F
          rw [pageOwn_congr W (rblStart B nl r) B rfl rfl rfl]
          iframe
          iframe #
          ipureintro
          exact ⟨Hlgv, Hd1, Hd2, HF, ⟨ρ.fl, rfl⟩, Hd3⟩
    · -- not a root
      have Hpn : r.nv.parent' ≠ null := Hif
      have HB0 := rblB_start W hwm bl B nl r dfc HB Hr Hdfc'
      have Hr0 : (rblStart B nl r).ns !! nl = some (rblClear r) := by
        show (<[nl := rblClear r]> B.ns) !! nl = _; rw [GMap.lookup_insert]
      obtain ⟨Hkey', rp, i, w, Hrp0, Hw, Hwp, Hwk, -⟩ :=
        (HB0.2.1.choose_spec.2.2 nl (rblClear r) Hr0).2.1 Hpn
      have Hpnl : r.nv.parent' ≠ nl := by
        intro he
        obtain ⟨ht, hh⟩ := HB.2.2.1
        have := hh nl r Hr Hpn; rw [he] at this; omega
      have Hrp : B.ns !! r.nv.parent' = some rp := by
        change (<[nl := rblClear r]> B.ns) !! r.nv.parent' = some rp at Hrp0
        rw [rf_lookup, if_neg Hpnl] at Hrp0; exact Hrp0
      wp_apply hnc $$ [Hn] as Hn
      · iframe
      try wp_auto
      wp_if_destruct
      · -- an empty leaf: removed
        have Hemp : r.ws = [] := by
          apply List.eq_nil_of_length_eq_zero
          have Hif0 : r.nv.inodes'.len = W64 0 := by simpa using Hif
          rw [← Hlen, Hsl.1, Hif0]; rfl
        have Hleaf : r.nv.isLeaf' = true := by
          rcases Bool.eq_false_or_eq_true r.nv.isLeaf' with h | h
          · exact h
          · have := (HNC.2.2.2.2.2.2.2.2.2.2.2.1 h).1; rw [Hemp] at this; cases this
        have HNP := HB.1.2.2.2.2.2.2.2.1 _ rp Hrp
        have Hrpd : Std.get? (Std.delete B.ns nl) r.nv.parent' = some rp := by
          show (GMap.delete nl B.ns) !! r.nv.parent' = _
          rw [GMap.lookup_delete_ne _ (Ne.symm Hpnl)]; exact Hrp
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
          Hrpd).1 $$ Hns with ⟨Hp, Hns⟩
        isimp only [nodeOwn] at Hp
        icases Hp with ⟨Hpn', Hpins, Hpcap, Hpents, Hpch, Hpchcap, Hpkey⟩
        icases (pv_half W.data W.ps W.pages W.q).1 $$ Hpv with ⟨Hpv1, Hpv2⟩
        icases nodeBorrow W HvOK.1 rp.ws rp.ins W.q.half HNP.2.2.2.2.1 $$ [Hpv1 Hpents]
          with ⟨%es, %Hm, Hes, Hpback⟩
        · iframe
        have Hks : r.ksrc ≠ Src.stale := by
          rcases HNC.2.2.2.2.2.2.2.2.2.1 with h | h
          · exact absurd h Hkey'
          · exact h.2
        icases keyBorrow W HvOK.1 W.q.half r.nv.key' r.ksrc r.key Hks $$ [Hpv2 Hkey]
          with ⟨%dk, %ck, %Hck, Hk, Hkback⟩
        · iframe
        have Hck' : ck = r.key := Hck Hkey'
        have Hes_sorted : entriesSorted es := (wMatch_sorted _ _ Hm).2 HNP.2.2.1
        have Hil : i < rp.ws.length := (List.getElem?_eq_some_iff.1 Hw).1
        have Hesk : entryKey es i = ck := by
          rw [wMatch_key rp.ws es Hm, Hck']; unfold wKey; rw [Hw]; exact Hwk
        wp_apply hdel _ rp.nv rp.ins es r.nv.key' ck dk Hes_sorted $$ [Hpn' Hpins Hpcap Hes Hk]
          as %idx ⟨%Hidx, Hk, Hd⟩
        · iframe
        have Hidx' : sint.nat idx = i :=
          searchIdx_eq es Hes_sorted ck i (by rw [← wMatch_length Hm]; exact Hil) Hesk _ Hidx.2
        rw [decide_eq_true (show sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = ck by
          rw [Hidx', ← wMatch_length Hm]; exact ⟨Hil, Hesk⟩), if_pos rfl]
        icases Hd with ⟨%it, %e, %Hie, Hite, Hpn', Hpins, Hpcap, Hes⟩
        rw [Hidx'] at Hie
        ihave Hes := inodesOwn_undel rp.ins es i it e Hie.1 Hie.2 $$ [Hes Hite]
        · rw [Hidx']; iframe
        ihave Hk := Hkback $$ Hk
        icases Hk with ⟨Hpv2, Hkey⟩
        ihave Hes := Hpback $$ Hes
        icases Hes with ⟨Hpv1, Hpents⟩
        ihave Hpv := (pv_half W.data W.ps W.pages W.q).2 $$ [Hpv1 Hpv2]
        · iframe
        ihave %Hplen := BigSepL2.bigSepL2_length $$ Hpents
        ihave Hpents := bigSepL2_eraseIdx (fun it w => wOwn (GF := GF) W it w) rp.ins rp.ws i Hplen
          (by rw [Hplen]; exact Hil) $$ Hpents
        try wp_auto
        have Hin : nl ∈ rp.cs :=
          (rm_basic W hwm bl _ nl (rblClear r) _ rp i w HB0.1 Hr0 Hleaf rfl Hpn Hrp0 Hw Hwp).2.1
        wp_apply hrc _ _ rp.cs nl $$ [Hpn' Hpch Hpchcap] as Hrc
        · iframe
        rw [if_pos (decide_eq_true Hin)]
        icases Hrc with ⟨Hpn', Hpch, Hpchcap⟩
        try wp_auto
        wp_apply (wp_mapDelete (K := w64) (V := Loc) B.bv.nodes' B.nm r.nv.pgid'
          internal.common.Pgid.ty (go.GoType.PointerType node.ty)) $$ [Hnm] as Hnm
        · iframe
        try wp_auto
        have Hbas := rm_basic W hwm bl _ nl (rblClear r) _ rp i w HB0.1 Hr0 Hleaf rfl Hpn Hrp0 Hw Hwp
        ihave Htk : bktToks γ W (rblStart B nl r) $$ [Htk]
        · unfold rblStart; iapply (bktToks_set γ W B nl r (rblClear r) Hr (nrecEq_clear r)).2; iexact Htk
        icases rm_toks W hwm bl (rblStart B nl r) nl (rblClear r) r.nv.parent' rp i w
          (slice.slice rp.nv.inodes' Inode (W64 0) (rp.nv.inodes'.len - W64 1))
          (slice.slice rp.nv.children' Loc (W64 0) (rp.nv.children'.len - W64 1))
          HB0.1 Hr0 Hleaf Hemp rfl Hpn Hrp0 Hw Hwp γ $$ Htk with ⟨Htk, Hpt⟩
        ihave Hv : wView W $$ [Hdata Hfli Hpv]
        · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
        ihave Htxr : rblTx txl st1 pmap mp mv W.dbl $$ [Hst Hpf Hpm Hdbf Hmf Hmv]
        · unfold rblTx; iframe
        wp_apply hfree I γd γ W hwm txl txid ρ bl B.bv (DFrac.own 1) st1 pmap mp mv F nl
          ({ r.nv with bucket' := bl, unbalanced' := false } : node) hFree HvOK Htx
          rfl Hmtx HF (fun _ => HNC.2.2.2.2.2.2.2.2.1 Hbas.2.2.2.2.2.2.2.2.2)
          $$ [Hn Hbv Hv Htxr Hdbw HFt Hpt] as ⟨%ρ1, %F1, Hn, Hbv, Hv, Htxr, Hdbw, HFt, %Hf1⟩
        · iframe
        try wp_auto
        obtain ⟨HB1, Hent1, -, Hrp1, -⟩ := rbl_rm W hwm bl (rblStart B nl r) nl (rblClear r) r.nv.parent' rp
          i w (slice.slice rp.nv.inodes' Inode (W64 0) (rp.nv.inodes'.len - W64 1))
          (slice.slice rp.nv.children' Loc (W64 0) (rp.nv.children'.len - W64 1))
          HB0 Hr0 Hleaf Hemp rfl Hpn Hrp0 Hw Hwp
        have Hnseq : (GMap.delete nl (<[nl := rblClear r]> B.ns) : GMap Loc NRec) = GMap.delete nl B.ns := by
          apply GMap.ext; intro y
          by_cases hy : y = nl
          · subst hy; rw [GMap.lookup_delete, GMap.lookup_delete]
          · rw [GMap.lookup_delete_ne _ (Ne.symm hy), GMap.lookup_delete_ne _ (Ne.symm hy),
              GMap.lookup_insert_ne _ _ (Ne.symm hy)]
        ihave Hns := ns_reins W (Std.delete B.ns nl) r.nv.parent'
          (rmParent rp i nl (slice.slice rp.nv.inodes' Inode (W64 0) (rp.nv.inodes'.len - W64 1))
            (slice.slice rp.nv.children' Loc (W64 0) (rp.nv.children'.len - W64 1)))
          $$ [Hns Hpn' Hpins Hpcap Hpents Hpch Hpchcap Hpkey]
        · iframe; unfold nodeOwn rmParent; simp only; rw [Hidx']; iframe
        ihave Hb : bktOwn W bl (rmBkt (rblStart B nl r) nl r.nv.parent' (rblClear r).nv.pgid'
            (rmParent rp i nl (slice.slice rp.nv.inodes' Inode (W64 0) (rp.nv.inodes'.len - W64 1))
              (slice.slice rp.nv.children' Loc (W64 0) (rp.nv.children'.len - W64 1)))) $$
          [Hbv Hib Hnm Hbm Hpo Hns]
        · unfold bktOwn
          rw [pageOwn_congr W (rmBkt (rblStart B nl r) nl r.nv.parent' (rblClear r).nv.pgid'
            (rmParent rp i nl (slice.slice rp.nv.inodes' Inode (W64 0) (rp.nv.inodes'.len - W64 1))
              (slice.slice rp.nv.children' Loc (W64 0) (rp.nv.children'.len - W64 1)))) B rfl rfl rfl]
          simp only [rmBkt, rblStart]
          rw [Hnseq]
          iframe
        wp_apply IH $$ %I %γd %γ %W %hwm %txl %txid %ρ1 %bl %_ %st1 %pmap %mp %mv %F1 %r.nv.parent'
            %(rmParent rp i nl (slice.slice rp.nv.inodes' Inode (W64 0) (rp.nv.inodes'.len - W64 1))
              (slice.slice rp.nv.children' Loc (W64 0) (rp.nv.children'.len - W64 1)))
            %(some r.nv.parent') [] [Hb Hv Htxr Hdbw Htk HFt]
          as ⟨%B2, %st2, %ρ2, %F2, Hb, Hv, Htxr, Hdbw, Htk, HFt, %Hpost⟩
        · ipureintro
          exact ⟨hFree, HvOK, HB1, Htx, Hrp1, Or.inr ⟨rfl, rfl⟩, Hmtx, Hf1.1⟩
        · isimp only [bktOwn, wView, rblTx] at Hb Hv Htxr; iframe
        try wp_auto
        iapply HΦ
        iexists B2, st2, ρ2, F2
        iframe
        ipureintro
        obtain ⟨P1, P2, P3, ⟨fl2, P4⟩, P5⟩ := Hpost
        obtain ⟨-, ⟨fl1, Hρ1⟩⟩ := Hf1
        refine ⟨P1, rblStep_comp B _ B2 nl r.nv.parent' (rblPre_rm B nl r _ _) P2, P3,
          ⟨fl2, by rw [P4, Hρ1]⟩, fun k v he => P5 k v (Hent1 k v ?_)⟩
        exact entryIn_sim W (bktSim_set B nl r (rblClear r) Hr (nrecEq_clear r)) k v he
      · -- a node with entries: merged with a sibling
        have Hne : 0 < r.ws.length := by
          rw [← Hlen, Hsl.1]
          have : r.nv.inodes'.len ≠ W64 0 := by simpa using Hif
          have : sint.nat r.nv.inodes'.len ≠ 0 := by intro h; apply this; word
          omega
        have HNP := HB.1.2.2.2.2.2.2.2.1 _ rp Hrp
        obtain ⟨rq, Hrq, Hpbr, -⟩ := HNC.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Hpn
        rw [Hrp] at Hrq; cases Hrq
        have Hp2 : 2 ≤ rp.ws.length :=
          ((HB0.2.1.choose_spec.2.2 _ rp Hrp0).2.2.1 Hpbr).1 (fun h => Hpnl (Option.some.inj h).symm)
        have Hrpd : Std.get? (Std.delete B.ns nl) r.nv.parent' = some rp := by
          show (GMap.delete nl B.ns) !! r.nv.parent' = _
          rw [GMap.lookup_delete_ne _ (Ne.symm Hpnl)]; exact Hrp
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
          Hrpd).1 $$ Hns with ⟨Hp, Hns⟩
        isimp only [nodeOwn] at Hp
        icases Hp with ⟨Hpn', Hpins, Hpcap, Hpents, Hpch, Hpchcap, Hpkey⟩
        ihave %Hpsl := ownSlice_len _ _ _ $$ Hpins
        ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
        · iPkgInit
        wp_apply hnc $$ [Hpn'] as Hpn'
        · iframe
        try wp_auto
        have Hplen : rp.ins.length = rp.ws.length := HNP.2.1
        rw [decide_eq_true (show sint.Z (W64 1) < sint.Z rp.nv.inodes'.len by
          have : 2 ≤ sint.nat rp.nv.inodes'.len := by rw [← Hpsl.1, Hplen]; exact Hp2
          have := Hpsl.2
          word)]
        wp_apply hA
        try wp_auto
        icases (pv_half W.data W.ps W.pages W.q).1 $$ Hpv with ⟨Hpv1, Hpv2⟩
        icases nodeBorrow W HvOK.1 rp.ws rp.ins W.q.half HNP.2.2.2.2.1 $$ [Hpv1 Hpents]
          with ⟨%es, %Hm, Hes, Hpback⟩
        · iframe
        have Hks : r.ksrc ≠ Src.stale := by
          rcases HNC.2.2.2.2.2.2.2.2.2.1 with h | h
          · exact absurd h Hkey'
          · exact h.2
        icases keyBorrow W HvOK.1 W.q.half r.nv.key' r.ksrc r.key Hks $$ [Hpv2 Hkey]
          with ⟨%dk, %ck, %Hck, Hk, Hkback⟩
        · iframe
        have Hck' : ck = r.key := Hck Hkey'
        have Hes_sorted : entriesSorted es := (wMatch_sorted _ _ Hm).2 HNP.2.2.1
        have Hil : i < rp.ws.length := (List.getElem?_eq_some_iff.1 Hw).1
        have Hesk : entryKey es i = ck := by
          rw [wMatch_key rp.ws es Hm, Hck']; unfold wKey; rw [Hw]; exact Hwk
        wp_apply hci _ rp.nv (DFrac.own 1) rp.ins (DFrac.own 1) es nl
          ({ r.nv with bucket' := bl, unbalanced' := false } : node) (DFrac.own 1) ck dk Hes_sorted
          $$ [Hpn' Hpins Hes Hn Hk] as %idx ⟨%Hidx, Hpn', Hpins, Hes, Hn, Hk⟩
        · iframe
        have Hidx' : sint.nat idx = i :=
          searchIdx_eq es Hes_sorted ck i (by rw [← wMatch_length Hm]; exact Hil) Hesk _ Hidx.2
        ihave Hk := Hkback $$ Hk
        icases Hk with ⟨Hpv2, Hkey⟩
        ihave Hes := Hpback $$ Hes
        icases Hes with ⟨Hpv1, Hpents⟩
        ihave Hpv := (pv_half W.data W.ps W.pages W.q).2 $$ [Hpv1 Hpv2]
        · iframe
        try wp_auto
        ihave Hns := (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
          Hrpd).2 $$ [Hns Hpn' Hpins Hpcap Hpents Hpch Hpchcap Hpkey]
        · iframe; unfold nodeOwn; iframe
        ihave Hns := ns_reins W B.ns nl (rblClear r) $$ [Hns Hn Hins Hcap Hents Hch Hchcap Hkey]
        · iframe; unfold nodeOwn; simp only [rblClear]; rw [Hbl]; iframe
        ihave Hb : bktOwn W bl (rblStart B nl r) $$ [Hbv Hib Hnm Hbm Hpo Hns]
        · unfold bktOwn; rw [pageOwn_congr W (rblStart B nl r) B rfl rfl rfl]; iframe
        ihave Hv : wView W $$ [Hdata Hfli Hpv]
        · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
        ihave Htk : bktToks γ W (rblStart B nl r) $$ [Htk]
        · unfold rblStart; iapply (bktToks_set γ W B nl r (rblClear r) Hr (nrecEq_clear r)).2; iexact Htk
        have HsOK := rbl_siblingOK W hwm bl (rblStart B nl r) (some nl) HvOK HB0 nl (rblClear r) Hr0 Hpn Hks
        have Hwss : wsSorted rp.ws := HNP.2.2.1
        have Hwki : wKey rp.ws i = (rblClear r).key := by unfold wKey; rw [Hw]; exact Hwk
        have HnlB : ∀ B1 : BRec, rblB W hwm bl B1 (some nl) → ∀ rn1, B1.ns !! nl = some rn1 →
            rn1.nv.pgid' = (rblClear r).nv.pgid' → B1.nm !! w.pgid = some nl := by
          intro B1 HB1 rn1 hrn1 hpg1
          rw [Hwp, ← hpg1]; exact (HB1.1.2.2.2.2.2.2.2.1 nl rn1 hrn1).2.2.2.2.2.2.1
        wp_join (iprop(∃ (nn ll lr : Loc) (B1 : BRec) (st2 : TxStats) (k : Nat) (wl wr : WEntry)
            (rp1 rl rr : NRec),
          n_ptr ↦ nn ∗ leftNode_ptr ↦ ll ∗ rightNode_ptr ↦ lr ∗ bktOwn W bl B1 ∗ wView W ∗
          structFieldRef Tx go!"stats" txl ↦ st2 ∗ structFieldRef Tx go!"pages" txl ↦ pmap ∗
          pmap ↦$ (∅ : GMap w64 Loc) ∗ structFieldRef Tx go!"db" txl ↦ W.dbl ∗ bktToks γ W B1 ∗
          ⌜(nn = ll ∨ nn = lr) ∧ (nl = ll ∨ nl = lr) ∧ rblB W hwm bl B1 (some nl) ∧
            (∀ k v, entryIn W (rblStart B nl r) k v → entryIn W B1 k v) ∧
            B1.bv = B.bv ∧ B1.ib = B.ib ∧ B1.bm = B.bm ∧
            (∀ y ry', B1.ns !! y = some ry' → ry'.nv.unbalanced' = true →
              ∃ ry, (rblStart B nl r).ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
                ry'.nv.pgid' = ry.nv.pgid') ∧
            B1.ns !! r.nv.parent' = some rp1 ∧ rp1.nv.isLeaf' = false ∧ rp1.ws[k]? = some wl ∧
            rp1.ws[k + 1]? = some wr ∧ B1.nm !! wl.pgid = some ll ∧ B1.nm !! wr.pgid = some lr ∧
            B1.ns !! ll = some rl ∧ B1.ns !! lr = some rr ∧ 0 < (rl.ws ++ rr.ws).length⌝) : IProp GF)
          with [n Hb Hv Htk Hst Hpf Hpm Hdbf leftNode rightNode]
          as ⟨%nn, %ll, %lr, %B1, %st2, %k, %wl, %wr, %rp1, %rl, %rr, n, Hleft, Hright, Hb, Hv, Hst, Hpf,
            Hpm, Hdbf, Htk, %HR⟩
        · -- the next sibling
          have Hi0 : i = 0 := by rw [← Hidx']; rfl
          try wp_auto
          wp_apply hnext W bl (rblStart B nl r) txl st1 pmap ∅ (DFrac.own 1) nl (rblClear r) HvOK Htx Hr0
            HsOK (fun _ => Hkey') $$ [Hb Hv Hst Hpf Hpm Hdbf] as %l %B1 %st2 ⟨Hb, Hv, Hst, Hpf, Hpm, Hdbf, %Hsib⟩
          · iframe
          try wp_auto
          rcases Hsib with ⟨hpn0, -⟩ | ⟨rp', j, hrp', hjs, ⟨hlen, -⟩ | ⟨i', w', p, pg, src, hi', hw', hsrc, hres⟩⟩
          · exact absurd hpn0 Hpn
          · rw [Hrp0] at hrp'; cases hrp'
            have := wSearch_eq rp.ws Hwss _ i Hil Hwki j hjs; simp only [↓reduceIte] at hlen; omega
          · rw [Hrp0] at hrp'; cases hrp'
            have hj := wSearch_eq rp.ws Hwss _ i Hil Hwki j hjs
            simp only [↓reduceIte] at hi'
            icases rbl_nodeRes γ W hwm bl (rblStart B nl r) (some nl) ∅ (rblClear r).nv.parent' rp i' w' p pg
              src l B1 st1 st2 HvOK HB0 Hrp0 Hpbr hw' hsrc hres $$ Htk with ⟨Htk, %HR⟩
            obtain ⟨HB1, Hent1, hbv1, hib1, hbm1, hlc1, ⟨rl, hrl, hpl⟩, hun1, hkeep1⟩ := HR
            obtain ⟨rn1, hrn1, hws1, -, -, -, hpg1⟩ := hkeep1 nl (rblClear r) Hr0
            obtain ⟨rp1, hrp1, hpws1, hplf1, -⟩ := hkeep1 _ rp Hrp0
            wp_join_done
            iexists nl, nl, l, B1, st2, 0, w, w', rp1, rn1, rl
            iframe
            ipureintro
            refine ⟨Or.inl rfl, Or.inl rfl, HB1, Hent1, hbv1, hib1, hbm1, hun1, hrp1,
              by rw [hplf1]; exact Hpbr, by rw [hpws1, ← Hi0]; exact Hw,
              by rw [hpws1, show 0 + 1 = i' by omega]; exact hw', HnlB B1 HB1 rn1 hrn1 hpg1, hlc1,
              hrn1, hrl, ?_⟩
            rw [List.length_append, hws1]; exact Nat.lt_of_lt_of_le Hne (Nat.le_add_right _ _)
        · -- the previous sibling
          have Hi0 : i ≠ 0 := by
            have h0 : ¬ idx = W64 0 := by assumption
            intro h; apply h0; rw [h] at Hidx'; word
          try wp_auto
          wp_apply hprev W bl (rblStart B nl r) txl st1 pmap ∅ (DFrac.own 1) nl (rblClear r) HvOK Htx Hr0
            HsOK (fun _ => Hkey') $$ [Hb Hv Hst Hpf Hpm Hdbf] as %l %B1 %st2 ⟨Hb, Hv, Hst, Hpf, Hpm, Hdbf, %Hsib⟩
          · iframe
          try wp_auto
          rcases Hsib with ⟨hpn0, -⟩ | ⟨rp', j, hrp', hjs, ⟨hj0, -⟩ | ⟨i', w', p, pg, src, hi', hw', hsrc, hres⟩⟩
          · exact absurd hpn0 Hpn
          · rw [Hrp0] at hrp'; cases hrp'
            have := wSearch_eq rp.ws Hwss _ i Hil Hwki j hjs; simp only [Bool.false_eq_true, ↓reduceIte] at hj0
            omega
          · rw [Hrp0] at hrp'; cases hrp'
            have hj := wSearch_eq rp.ws Hwss _ i Hil Hwki j hjs
            simp only [Bool.false_eq_true, ↓reduceIte] at hi'
            icases rbl_nodeRes γ W hwm bl (rblStart B nl r) (some nl) ∅ (rblClear r).nv.parent' rp i' w' p pg
              src l B1 st1 st2 HvOK HB0 Hrp0 Hpbr hw' hsrc hres $$ Htk with ⟨Htk, %HR⟩
            obtain ⟨HB1, Hent1, hbv1, hib1, hbm1, hlc1, ⟨rl, hrl, hpl⟩, hun1, hkeep1⟩ := HR
            obtain ⟨rn1, hrn1, hws1, -, -, -, hpg1⟩ := hkeep1 nl (rblClear r) Hr0
            obtain ⟨rp1, hrp1, hpws1, hplf1, -⟩ := hkeep1 _ rp Hrp0
            wp_join_done
            iexists nl, l, nl, B1, st2, i', w', w, rp1, rl, rn1
            iframe
            ipureintro
            refine ⟨Or.inr rfl, Or.inr rfl, HB1, Hent1, hbv1, hib1, hbm1, hun1, hrp1,
              by rw [hplf1]; exact Hpbr, by rw [hpws1]; exact hw',
              by rw [hpws1, show i' + 1 = i by omega]; exact Hw, hlc1, HnlB B1 HB1 rn1 hrn1 hpg1,
              hrl, hrn1, ?_⟩
            rw [List.length_append, hws1]; exact Nat.lt_of_lt_of_le Hne (Nat.le_add_left _ _)
        obtain ⟨Hnn, Hnl, HB1, Hent1, hbv1, hib1, hbm1, hun1, hrp1, hplf1, hwl, hwr, hll, hlr, hrl, hrr,
          hne⟩ := HR
        obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, hnmp, hnd, hroot0, hllin, hlrin, hself, hpgne,
          hppl⟩ := mg_basic W hwm bl B1 r.nv.parent' rp1 k wl wr ll lr rl rr HB1.1 HB1.2.2.1 Hpn hrp1 hplf1
            hwl hwr hll hlr hrl hrr
        icases dbWR_view_keep I γd W txl txid ρ $$ Hdbw with ⟨Hdbw, %Hdv⟩
        have hkind : rl.nv.isLeaf' = rr.nv.isLeaf' :=
          (rbl_mg W hwm bl B1 r.nv.parent' rp1 k wl wr ll lr rl rr nl slice.nil slice.nil slice.nil
            slice.nil HB1 Hnl Hdv.2 Hpn hrp1 hplf1 hwl hwr hll hlr hrl hrr hne).2.2.2
        have HNl := HB1.1.2.2.2.2.2.2.2.1 ll rl hrl
        have HNr := HB1.1.2.2.2.2.2.2.2.1 lr rr hrr
        have Hrlen : rr.ins.length = rr.ws.length := HNr.2.1
        have Hllen : rl.ins.length = rl.ws.length := HNl.2.1
        have Hlrn : lr ≠ null := (HB1.1.2.2.2.2.1 _ _ hlr).1
        isimp only [bktOwn] at Hb
        icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
          (show Std.get? B1.ns r.nv.parent' = some rp1 from hrp1)).1 $$ Hns with ⟨Hp, Hns⟩
        have hll' : Std.get? (Std.delete B1.ns r.nv.parent') ll = some rl := by
          show (GMap.delete r.nv.parent' B1.ns) !! ll = _
          rw [GMap.lookup_delete_ne _ (Ne.symm hllp)]; exact hrl
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
          hll').1 $$ Hns with ⟨Hl, Hns⟩
        have hlr' : Std.get? (Std.delete (Std.delete B1.ns r.nv.parent') ll) lr = some rr := by
          show (GMap.delete ll (GMap.delete r.nv.parent' B1.ns)) !! lr = _
          rw [GMap.lookup_delete_ne _ hllr, GMap.lookup_delete_ne _ (Ne.symm hlrp)]; exact hrr
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
          hlr').1 $$ Hns with ⟨Hr, Hns⟩
        isimp only [nodeOwn] at Hp Hl Hr
        icases Hp with ⟨Hpn', Hpins, Hpcap, Hpents, Hpch, Hpchcap, Hpkey⟩
        icases Hl with ⟨Hln, Hlins, Hlcap, Hlents, Hlch, Hlchcap, Hlkey⟩
        icases Hr with ⟨Hrn, Hrins, Hrcap, Hrents, Hrch, Hrchcap, Hrkey⟩
        ihave %Hrsl := ownSlice_len _ _ _ $$ Hrins
        ihave %Hrwf := ownSlice_wf _ _ _ $$ Hrins
        rcases Hnn with Hnn | Hnn <;> subst nn <;>
        · try wp_auto
          ihave IH2 : (∃ (j : w64) (sCr sCl : GoSlice) (csr : List Loc), "i" ∷ i_ptr ↦ j ∗
              "Hns" ∷ ([∗map] y ↦ ry ∈ Std.delete (Std.delete (Std.delete B1.ns r.nv.parent') ll) lr,
                nodeOwn (GF := GF) W y (repStep B1.nm lr ll rr.ws (sint.nat j) y ry)) ∗
              "Hrn" ∷ lr ↦ ({ rr.nv with bucket' := bl, parent' := r.nv.parent', children' := sCr } : node) ∗
              "Hrch" ∷ sCr ↦* csr ∗
              "Hrchcap" ∷ ownSliceCap Loc sCr (DFrac.own 1) ∗
              "Hln" ∷ ll ↦ ({ rl.nv with bucket' := bl, parent' := r.nv.parent', children' := sCl } : node) ∗
              "Hlch" ∷ sCl ↦* (rl.cs ++ kidsOf B1 (rr.ws.take (sint.nat j))) ∗
              "Hlchcap" ∷ ownSliceCap Loc sCl (DFrac.own 1) ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rr.nv.inodes'.len⌝ : IProp GF)
              $$ [i Hns Hrn Hrch Hrchcap Hln Hlch Hlchcap]
          · iexists W64 0, rr.nv.children', rl.nv.children', rr.cs
            simp only [named]
            rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero,
              show kidsOf B1 [] = [] from rfl, List.append_nil]
            simp only [repStep_zero]
            rw [show ({ rr.nv with bucket' := bl, parent' := r.nv.parent', children' := rr.nv.children' } :
                node) = rr.nv by rw [← HNr.1, ← hp2],
              show ({ rl.nv with bucket' := bl, parent' := r.nv.parent', children' := rl.nv.children' } :
                node) = rl.nv by rw [← HNl.1, ← hp1]]
            iframe
            ipureintro
            exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hrwf.1⟩
          wp_for IH2
          wp_if_destruct
          · have Hlt : sint.Z j < sint.Z rr.nv.inodes'.len := by
              first | assumption | exact Classical.byContradiction fun hc => false_neq_true (by rw [← decide_eq_false hc]; exact Hif)
            have Hjn : sint.nat j < rr.ins.length := by rw [Hrsl.1]; word
            list_elem rr.ins (sint.nat j) as it
            obtain ⟨x, Hx⟩ : ∃ x, rr.ws[sint.nat j]? = some x :=
              ⟨_, List.getElem?_eq_getElem (by rw [← Hrlen]; exact Hjn)⟩
            rw [ite_cond_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rr.nv.inodes'.len
              from ⟨Hj.1, Hlt⟩))]
            wp_apply wp_load_slice_index rr.nv.inodes' (sint.Z j) rr.ins _ it Hj.1 $$ [Hrins] with Hrins
            · iframe; ipureintro; exact Hit_lookup
            try wp_auto
            icases wOwn_at W rr.ins rr.ws (sint.nat j) it x Hit_lookup Hx $$ Hrents with ⟨%Hipx, Hrents⟩
            try wp_auto
            wp_apply hPgid $$ [$inode] as inode
            try wp_auto
            rw [Hipx.2]
            wp_apply (wp_map_lookup2 (K := w64) (V := Loc) internal.common.Pgid.ty
              (go.GoType.PointerType node.ty) B1.bv.nodes' B1.nm x.pgid (DFrac.own 1)) $$ [Hnm] as Hnm
            · iframe
            try wp_auto
            have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
            have htake : rr.ws.take (sint.nat j + 1) = rr.ws.take (sint.nat j) ++ [x] := by
              rw [List.take_succ, Hx]; rfl
            cases hcase : B1.nm !! x.pgid with
            | none =>
              simp only [Option.isSome_none, decide_false, Bool.false_eq_true]
              try wp_auto
              wp_for_post
              ihave Hns := rep_none W _ B1.nm lr ll rr.ws (sint.nat j) x Hx hcase $$ Hns
              iframe
              iexists j + W64 1, sCr, sCl, csr
              have hk1 : kidsOf B1 (rr.ws.take (sint.nat j + 1)) = kidsOf B1 (rr.ws.take (sint.nat j)) := by
                rw [htake]; unfold kidsOf; rw [List.filterMap_append]; simp [hcase]
              rw [hj1, hk1]
              iframe
              ipureintro
              exact ⟨by word, by word⟩
            | some c =>
              have hxin : x ∈ rr.ws := List.mem_of_getElem? Hx
              have hrrb : rr.nv.isLeaf' = false := by
                rcases Bool.eq_false_or_eq_true rr.nv.isLeaf' with h | h
                · exact absurd (leaf_nokid W hwm bl B1 (some nl) HB1 Hdv.2 hroot0 lr rr hrr h x hxin)
                    (by rw [hcase]; nofun)
                · exact h
              obtain ⟨-, hndr, hkids⟩ := HNr.2.2.2.2.2.2.2.2.2.2.2.1 hrrb
              obtain ⟨rc', hrc', hpc'⟩ := (hkids x hxin).2.1 c hcase
              have hcr : c ≠ lr := by
                intro he; rw [he, hrr] at hrc'; cases hrc'
                exact hself lr rr hrr (by rw [hpc']; exact Hlrn) hpc'
              have hcl : c ≠ ll := by
                intro he; rw [he, hrl] at hrc'; cases hrc'; rw [hp1] at hpc'; exact hlrp hpc'.symm
              have hcp : c ≠ r.nv.parent' :=
                mg_cyc W hwm bl B1 r.nv.parent' rp1 k wl wr ll lr rl rr HB1.1 HB1.2.2.1 Hpn hrp1 hplf1 hwl
                  hwr hll hlr hrl hrr c rc' hrc' (Or.inr hpc')
              have hD : (Std.delete (Std.delete (Std.delete B1.ns r.nv.parent') ll) lr : GMap Loc NRec) !! c =
                  some rc' := by
                show (GMap.delete lr (GMap.delete ll (GMap.delete r.nv.parent' B1.ns))) !! c = _
                rw [GMap.lookup_delete_ne _ (Ne.symm hcr), GMap.lookup_delete_ne _ (Ne.symm hcl),
                  GMap.lookup_delete_ne _ (Ne.symm hcp)]
                exact hrc'
              icases rep_hit W _ B1.nm lr ll rr.ws (sint.nat j) x Hx c hcase rc' hD $$ Hns
                with ⟨Hcc, Hback⟩
              rw [repStep_fresh B1.nm lr ll rr.ws (sint.nat j) x hndr c
                (fun p q hp hq => nm_inj W hwm bl B1 HB1.1 p q c hp hq) Hx hcase rc']
              isimp only [nodeOwn] at Hcc
              icases Hcc with ⟨Hcc, Hcc1, Hcc2, Hcc3, Hcc4, Hcc5, Hcc6⟩
              simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
              try wp_auto
              rw [hpc']
              wp_apply hrc lr ({ rr.nv with bucket' := bl, parent' := r.nv.parent', children' := sCr } : node) csr c
                $$ [Hrn Hrch Hrchcap] as Hrc
              · iframe
              ihave Hrc : (∃ (sC' : GoSlice) (cs' : List Loc),
                  lr ↦ ({ rr.nv with bucket' := bl, parent' := r.nv.parent', children' := sC' } : node) ∗
                  sC' ↦* cs' ∗ ownSliceCap Loc sC' (DFrac.own 1)) $$ [Hrc]
              · by_cases hin : c ∈ csr
                · rw [if_pos (decide_eq_true hin)]
                  icases Hrc with ⟨Hrn, Hrch, Hrchcap⟩
                  iexists _, _
                  try isimp only at Hrn
                  iframe
                · rw [if_neg (by simpa using hin)]
                  icases Hrc with ⟨Hrn, Hrch, Hrchcap⟩
                  iexists sCr, csr
                  iframe
              icases Hrc with ⟨%sCr', %csr', Hrn, Hrch, Hrchcap⟩
              try wp_auto
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %sl ⟨Hsl, -⟩
              wp_apply wp_slice_append $$ [$Hlch $Hlchcap $Hsl] as %s' ⟨Hlch, Hlchcap, -⟩
              try wp_auto
              ihave Hns := Hback $$ [Hcc Hcc1 Hcc2 Hcc3 Hcc4 Hcc5 Hcc6]
              · rw [repStep_hit B1.nm lr ll rr.ws (sint.nat j) x Hx c hcase rc' hpc']
                unfold nodeOwn; isimp only; iframe
              wp_for_post
              iframe
              iexists j + W64 1, sCr', s', csr'
              have hk1 : kidsOf B1 (rr.ws.take (sint.nat j + 1)) =
                  kidsOf B1 (rr.ws.take (sint.nat j)) ++ [c] := by
                rw [htake]; unfold kidsOf; rw [List.filterMap_append]; simp [hcase]
              rw [hj1, hk1, ← List.append_assoc]
              try isimp only at Hln
              iframe
              ipureintro
              exact ⟨by word, by word⟩
          have Hge : ¬ sint.Z j < sint.Z rr.nv.inodes'.len := by
            first | assumption | exact fun h => Hif (by rw [decide_eq_true h])
          try simp only [if_decide_bool_eq_false, decide_eq_false Hge, Bool.false_eq_true, ↓reduceIte,
            _root_.decide_true, decide_not, Bool.not_false]
          try wp_auto
          have Hjeq : sint.nat j = rr.ws.length := by rw [← Hrlen, Hrsl.1]; word
          have Htk_full : rr.ws.take rr.ws.length = rr.ws := List.take_of_length_le (Nat.le_refl _)
          rw [Hjeq, Htk_full]
          wp_apply wp_slice_append $$ [$Hlins $Hlcap $Hrins] as %sI ⟨Hlins, Hlcap, Hrins⟩
          try wp_auto
          obtain ⟨Hrkey', rq, iq, wq, hrq, hwq, hwqp, hwqk, -⟩ :=
            (HB1.2.1.choose_spec.2.2 lr rr hrr).2.1 (by rw [hp2]; exact Hpn)
          rw [hp2, hrp1] at hrq; cases hrq
          have hiq : iq = k + 1 := Classical.byContradiction fun h =>
            nodup_pgid_ne rp1.ws hnd (k + 1) iq wr wq hwr hwq h (hwqp.trans hpgr)
          subst hiq
          rw [hwr] at hwq; cases hwq
          have Hksr : rr.ksrc ≠ Src.stale := by
            rcases HNr.2.2.2.2.2.2.2.2.2.1 with h | h
            · exact absurd h Hrkey'
            · exact h.2
          isimp only [wView] at Hv
          icases Hv with ⟨Hdata, #Hps', #Hlg', Hfli, #Hdl', %Hlgv', Hpv⟩
          have HNP1 := HB1.1.2.2.2.2.2.2.2.1 _ rp1 hrp1
          icases (pv_half W.data W.ps W.pages W.q).1 $$ Hpv with ⟨Hpv1, Hpv2⟩
          icases nodeBorrow W HvOK.1 rp1.ws rp1.ins W.q.half HNP1.2.2.2.2.1 $$ [Hpv1 Hpents]
            with ⟨%es, %Hm, Hes, Hpback⟩
          · iframe
          icases keyBorrow W HvOK.1 W.q.half rr.nv.key' rr.ksrc rr.key Hksr $$ [Hpv2 Hrkey]
            with ⟨%dk, %ck, %Hck, Hk, Hkback⟩
          · iframe
          have Hck' : ck = rr.key := Hck Hrkey'
          have Hes_sorted : entriesSorted es := (wMatch_sorted _ _ Hm).2 HNP1.2.2.1
          have Hil : k + 1 < rp1.ws.length := (List.getElem?_eq_some_iff.1 hwr).1
          have Hesk : entryKey es (k + 1) = ck := by
            rw [wMatch_key rp1.ws es Hm, Hck']; unfold wKey; rw [hwr]; exact hwqk
          wp_apply hdel _ rp1.nv rp1.ins es rr.nv.key' ck dk Hes_sorted $$ [Hpn' Hpins Hpcap Hes Hk]
            as %idx ⟨%Hidx, Hk, Hd⟩
          · iframe
          have Hidx' : sint.nat idx = k + 1 :=
            searchIdx_eq es Hes_sorted ck (k + 1) (by rw [← wMatch_length Hm]; exact Hil) Hesk _ Hidx.2
          rw [decide_eq_true (show sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = ck by
            rw [Hidx', ← wMatch_length Hm]; exact ⟨Hil, Hesk⟩), if_pos rfl]
          icases Hd with ⟨%it, %e, %Hie, Hite, Hpn', Hpins, Hpcap, Hes⟩
          rw [Hidx'] at Hie
          ihave Hes := inodesOwn_undel rp1.ins es (k + 1) it e Hie.1 Hie.2 $$ [Hes Hite]
          · rw [Hidx']; iframe
          ihave Hk := Hkback $$ Hk
          icases Hk with ⟨Hpv2, Hrkey⟩
          ihave Hes := Hpback $$ Hes
          icases Hes with ⟨Hpv1, Hpents⟩
          ihave Hpv := (pv_half W.data W.ps W.pages W.q).2 $$ [Hpv1 Hpv2]
          · iframe
          ihave %Hplen1 := BigSepL2.bigSepL2_length $$ Hpents
          ihave Hpents := bigSepL2_eraseIdx (fun it w => wOwn (GF := GF) W it w) rp1.ins rp1.ws (k + 1)
            Hplen1 (by rw [Hplen1]; exact Hil) $$ Hpents
          try wp_auto
          wp_apply hrc _ _ rp1.cs lr $$ [Hpn' Hpch Hpchcap] as Hrc
          · iframe
          rw [if_pos (decide_eq_true hlrin)]
          icases Hrc with ⟨Hpn', Hpch, Hpchcap⟩
          try wp_auto
          wp_apply (wp_mapDelete (K := w64) (V := Loc) B1.bv.nodes' B1.nm rr.nv.pgid'
            internal.common.Pgid.ty (go.GoType.PointerType node.ty)) $$ [Hnm] as Hnm
          · iframe
          try wp_auto
          icases mg_toks γ W hwm bl B1 r.nv.parent' rp1 k wl wr ll lr rl rr HB1.1 HB1.2.2.1 Hpn hrp1 hplf1
            hwl hwr hll hlr hrl hrr sI sCl
            (slice.slice rp1.nv.inodes' Inode (W64 0) (rp1.nv.inodes'.len - W64 1))
            (slice.slice rp1.nv.children' Loc (W64 0) (rp1.nv.children'.len - W64 1)) hkind $$ Htk
            with ⟨Htk, Hpt⟩
          ihave Hv : wView W $$ [Hdata Hfli Hpv]
          · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
          ihave Htxr : rblTx txl st2 pmap mp mv W.dbl $$ [Hst Hpf Hpm Hdbf Hmf Hmv]
          · unfold rblTx; iframe
          wp_apply hfree I γd γ W hwm txl txid ρ bl B1.bv (DFrac.own 1) st2 pmap mp mv F lr
            ({ rr.nv with bucket' := bl, parent' := r.nv.parent', children' := sCr } : node) hFree HvOK
            (by rw [hbv1]; exact Htx) rfl Hmtx HF (fun _ => HNr.2.2.2.2.2.2.2.2.1 hroot0)
            $$ [Hrn Hbv Hv Htxr Hdbw HFt Hpt] as ⟨%ρ1, %F1, Hrn, Hbv, Hv, Htxr, Hdbw, HFt, %Hf1⟩
          · iframe
          simp only
          obtain ⟨Hmg1, Hmg2, Hmg3, -⟩ := rbl_mg W hwm bl B1 r.nv.parent' rp1 k wl wr ll lr rl rr nl sI sCl
            (slice.slice rp1.nv.inodes' Inode (W64 0) (rp1.nv.inodes'.len - W64 1))
            (slice.slice rp1.nv.children' Loc (W64 0) (rp1.nv.children'.len - W64 1))
            HB1 Hnl Hdv.2 Hpn hrp1 hplf1 hwl hwr hll hlr hrl hrr hne
          ihave Hns := mg_own W B1 r.nv.parent' ll lr rr.nv.pgid'
            (rmParent rp1 (k + 1) lr (slice.slice rp1.nv.inodes' Inode (W64 0) (rp1.nv.inodes'.len - W64 1))
              (slice.slice rp1.nv.children' Loc (W64 0) (rp1.nv.children'.len - W64 1)))
            (mgLeft rl rr (kidsOf B1 rr.ws) sI sCl) rr.ws hllp
            (fun y ry hy _ _ _ hp => kid_pos W hwm bl B1 HB1.1 lr rr Hlrn hrr y ry hy hp)
            $$ [Hns Hln Hlins Hlcap Hlents Hrents Hlch Hlchcap Hlkey Hpn' Hpins Hpcap Hpents Hpch Hpchcap Hpkey]
          · iframe Hns
            isplitl [Hln Hlins Hlcap Hlents Hrents Hlch Hlchcap Hlkey]
            · unfold nodeOwn mgLeft
              try isimp only
              try isimp only at Hln
              rw [HNl.1, hp1]
              iframe
            · unfold nodeOwn rmParent; simp only; rw [Hidx']; iframe
          ihave Hb : bktOwn W bl (mgBkt B1 r.nv.parent' ll lr rr.nv.pgid'
              (rmParent rp1 (k + 1) lr (slice.slice rp1.nv.inodes' Inode (W64 0) (rp1.nv.inodes'.len - W64 1))
                (slice.slice rp1.nv.children' Loc (W64 0) (rp1.nv.children'.len - W64 1)))
              (mgLeft rl rr (kidsOf B1 rr.ws) sI sCl)) $$ [Hbv Hib Hnm Hbm Hpo Hns]
          · unfold bktOwn
            rw [pageOwn_congr W (mgBkt B1 r.nv.parent' ll lr rr.nv.pgid'
              (rmParent rp1 (k + 1) lr (slice.slice rp1.nv.inodes' Inode (W64 0) (rp1.nv.inodes'.len - W64 1))
                (slice.slice rp1.nv.children' Loc (W64 0) (rp1.nv.children'.len - W64 1)))
              (mgLeft rl rr (kidsOf B1 rr.ws) sI sCl)) B1 rfl rfl rfl]
            simp only [mgBkt]
            iframe
          wp_apply IH $$ %I %γd %γ %W %hwm %txl %txid %ρ1 %bl %_ %st2 %pmap %mp %mv %F1 %r.nv.parent'
              %(rmParent rp1 (k + 1) lr (slice.slice rp1.nv.inodes' Inode (W64 0) (rp1.nv.inodes'.len - W64 1))
                (slice.slice rp1.nv.children' Loc (W64 0) (rp1.nv.children'.len - W64 1)))
              %(some r.nv.parent') [] [Hb Hv Htxr Hdbw Htk HFt]
            as ⟨%B3, %st3, %ρ3, %F3, Hb, Hv, Htxr, Hdbw, Htk, HFt, %Hpost⟩
          · ipureintro
            exact ⟨hFree, HvOK, Hmg1, by show B1.bv.tx' = txl; rw [hbv1]; exact Htx,
              by rw [mg_ns, if_pos rfl], Or.inr ⟨rfl, rfl⟩, Hmtx, Hf1.1⟩
          · isimp only [bktOwn, wView, rblTx] at Hb Hv Htxr; iframe
          try wp_auto
          iapply HΦ
          iexists B3, st3, ρ3, F3
          iframe
          ipureintro
          obtain ⟨P1, P2, P3, ⟨fl3, P4⟩, P5⟩ := Hpost
          obtain ⟨-, ⟨fl1, Hρ1⟩⟩ := Hf1
          refine ⟨P1, rblStep_comp B _ B3 nl r.nv.parent'
            (mg_pre B B1 (mgBkt B1 r.nv.parent' ll lr rr.nv.pgid'
              (rmParent rp1 (k + 1) lr (slice.slice rp1.nv.inodes' Inode (W64 0) (rp1.nv.inodes'.len - W64 1))
                (slice.slice rp1.nv.children' Loc (W64 0) (rp1.nv.children'.len - W64 1)))
              (mgLeft rl rr (kidsOf B1 rr.ws) sI sCl)) nl r.nv.parent' lr r hbv1 hib1 hbm1 hun1 rfl rfl rfl
              Hmg3) P2, P3,
            ⟨fl3, by rw [P4, Hρ1]⟩, fun kk v he => P5 kk v (Hmg2 kk v (Hent1 kk v ?_))⟩
          exact entryIn_sim W (bktSim_set B nl r (rblClear r) Hr (nrecEq_clear r)) kk v he


theorem node.rebalance.wp_sproof (hInc : TxStats.IncRebalance.spec (GF := GF) (hG := hG))
    (hsize : node.size.spec (GF := GF) (hG := hG))
    (hmin : node.minKeys.spec (GF := GF) (hG := hG))
    (hPgid : Inode.Pgid.spec (GF := GF) (hG := hG))
    (hnode : Bucket.node.spec (GF := GF) (hG := hG))
    (hfree : node.free.sspec (GF := GF) (hG := hG))
    (hnc : node.numChildren.spec (GF := GF) (hG := hG))
    (hdel : node.del.spec (GF := GF) (hG := hG))
    (hrc : node.removeChild.spec (GF := GF) (hG := hG))
    (hA : Assert.spec (GF := GF) (hG := hG))
    (hci : node.childIndex.spec (GF := GF) (hG := hG))
    (hnext : node.nextSibling.sspec (GF := GF) (hG := hG))
    (hprev : node.prevSibling.sspec (GF := GF) (hG := hG)) :
    node.rebalance.sspec (GF := GF) (hG := hG) := by
  intro I γd γ W hwm txl txid ρ bl B st pmap mp mv F nl r dfc H1 H2 H3 H4 H5 H6 H7 H8
  have H := rebal_loeb hInc hsize hmin hPgid hnode hfree hnc hdel hrc hA hci hnext hprev
  unfold rebalIw at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %I %γd %γ %W %hwm %txl %txid %ρ %bl %B %st %pmap %mp %mv %F %nl %r %dfc [] [HP] HΦ
  · ipureintro; exact ⟨H1, H2, H3, H4, H5, H6, H7, H8⟩
  · iexact HP

end proof

end bbolt
end EtcdGrove
end Perennial
