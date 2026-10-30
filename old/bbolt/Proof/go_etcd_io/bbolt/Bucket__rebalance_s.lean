module
public import Spec.go_etcd_io.bbolt.Bucket__rebalance_s
public import Spec.go_etcd_io.bbolt.node__rebalance_s

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

/-- `Bucket.rebalance.sspec`, as an Iris proposition (for the recursion). -/
def rebalBw : IProp GF :=
  iprop(∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (ρ : DBState) (T : WTx) (F : GMap Nat (List w8)) (bl : Loc),
  ⌜I.FreeSpec ∧ (T.bs !! bl).isSome ∧ T.mv.txid' = txid ∧ rblTxOK W (uint.nat T.mv.pgid') T ∧
    freedOK W ρ.fl txid F⌝ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ txShapeR γ W T ∗
      dbWR I γd W txl txid ρ ∗ pgToks γ F }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8)),
      ownWriteTx W txl T' ∗ txShapeR γ W T' ∗ dbWR I γd W txl txid ρ' ∗ pgToks γ F' ∗
      ⌜rblTxOK W (uint.nat T.mv.pgid') T' ∧ rblTxRel W T T' ∧ balancedFrom T' bl ∧
        freedOK W ρ'.fl txid F' ∧ (∃ fl, ρ' = { ρ with fl := fl })⌝ }})

set_option maxHeartbeats 3000000 in
theorem rebalB_loeb (hnr : node.rebalance.sspec (GF := GF) (hG := hG)) : ⊢ rebalBw (GF := GF) := by
  iloeb as IH
  unfold rebalBw
  iintro %I %γd %γ %W %txl %txid %ρ %T %F %bl %Hpre
  obtain ⟨hFree, HbS, Hmtx, HOK, HF⟩ := Hpre
  obtain ⟨B, HB⟩ := Option.isSome_iff_exists.1 HbS
  wp_start as ⟨Hown, Hsh, Hdbw, HFt⟩
  icases ownWriteTx_bkt_acc W txl T bl B HB $$ Hown with ⟨%Hok, Hrest, Hm, Hpm, Hb, Hv, Hclose⟩
  icases txShapeR_acc γ W T bl B HB $$ Hsh with ⟨Htk, Hshc⟩
  obtain ⟨HvOK, Hcl⟩ := Hok
  obtain ⟨hw1, hdb, hdbn, hpm0, -, -, -, hbk⟩ := Hcl
  obtain ⟨Htx, Hbc, Hkids⟩ := hbk bl B HB
  isimp only [TxW_rest_root] at Hrest
  icases Hrest with ⟨Hwr, Hmg, Hdb, Hmeta, Hpages, Hstats, Hch, Hwf, %Hnn⟩
  rw [hpm0]
  icases (bktOwn_NN W bl B).1 $$ Hb with ⟨Hb, Hnm⟩
  ihave Htxr : rblTx txl T.t.stats' T.t.pages' T.t.meta' T.mv W.dbl $$ [Hstats Hpages Hpm Hdb Hmeta Hm]
  · unfold rblTx; rw [← hdb]; iframe
  isimp only [bktOwnNN] at Hb
  icases Hb with ⟨Hbv, Hib, Hbm, Hpo, Hns⟩
  wp_auto
  try wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (keys : List w64) (i : Nat) (m' : GMap w64 Loc) =>
      iprop(∃ (B' : BRec) (st' : TxStats) (ρ' : DBState) (F' : GMap Nat (List w8)) (nv : Loc),
        n_ptr ↦ nv ∗ bktOwnNN W bl B' ∗ wView W ∗ rblTx txl st' T.t.pages' T.t.meta' T.mv W.dbl ∗
        dbWR I γd W txl txid ρ' ∗ bktToks γ W B' ∗ pgToks γ F' ∗
        ⌜B'.nm = m' ∧ B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.bm = B.bm ∧
          rblB W (uint.nat T.mv.pgid') bl B' none ∧
          (∀ l r, B'.ns !! l = some r → r.nv.unbalanced' = true → r.nv.pgid' ∈ keys.drop i) ∧
          (∀ l r', B'.ns !! l = some r' → r'.nv.unbalanced' = true →
            ∃ r, B.ns !! l = some r ∧ r.nv.unbalanced' = true) ∧
          freedOK W ρ'.fl txid F' ∧ (∃ fl, ρ' = { ρ with fl := fl }) ∧
          (∀ k v, entryIn W B k v → entryIn W B' k v)⌝)) $$ Hnm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [n Hbv Hib Hbm Hpo Hns Hv Htxr Hdbw Htk HFt]
  · iexists B, T.t.stats', ρ, F, _
    iframe
    isplitl [Hbv Hib Hbm Hpo Hns]
    · unfold bktOwnNN; iframe
    ipureintro
    refine ⟨rfl, rfl, rfl, rfl, HOK bl B HB, fun l r hl _ => ?_, fun l r hl hu => ⟨r, hl, hu⟩, HF,
      ⟨ρ.fl, rfl⟩, fun _ _ h => h⟩
    rw [List.drop_zero]
    exact (Hkset _).2 (by rw [(Hbc.2.2.2.2.2.2.2.1 l r hl).2.2.2.2.2.2.1]; rfl)
  isplitr
  · iintro !> %i %key %v %m' ⟨%Hk, %Hm'⟩ HP Hnm
    icases HP with ⟨%B1, %st1, %ρ1, %F1, %nv, Hn, HbNN, Hv, Htxr, Hdbw, Htk, HFt, %HP1⟩
    obtain ⟨hnm1, hbv1, hib1, hbm1, HB1, hpk1, hun1, hF1, ⟨fl1, hρ1⟩, hent1⟩ := HP1
    have hv1 : B1.nm !! key = some v := by rw [hnm1]; exact Hm'
    obtain ⟨-, r, hr, hpg⟩ := HB1.1.2.2.2.2.1 _ _ hv1
    ihave Hnm : B1.bv.nodes' ↦$ B1.nm $$ [Hnm]
    · rw [hbv1, hnm1]; iexact Hnm
    ihave Hb := (bktOwn_NN W bl B1).2 $$ [HbNN Hnm]
    · iframe
    try wp_auto
    wp_apply hnr I γd γ W (uint.nat T.mv.pgid') txl txid ρ1 bl B1 st1 T.t.pages' T.t.meta' T.mv F1 v r
      none hFree HvOK HB1 (by rw [hbv1]; exact Htx) hr (Or.inl rfl) Hmtx hF1
      $$ [Hb Hv Htxr Hdbw Htk HFt] as ⟨%B2, %st2, %ρ2, %F2, Hb, Hv, Htxr, Hdbw, Htk, HFt, %Hpost⟩
    · iframe
    try wp_auto
    obtain ⟨P1, P2, P3, ⟨fl2, P4⟩, P5⟩ := Hpost
    icases (bktOwn_NN W bl B2).1 $$ Hb with ⟨HbNN, Hnm⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists B2.nm
    ihave Hnm : B.bv.nodes' ↦$ B2.nm $$ [Hnm]
    · rw [← P2.1.trans hbv1]; iexact Hnm
    iframe Hnm
    iexists B2, st2, ρ2, F2, v
    iframe
    ipureintro
    refine ⟨rfl, P2.1.trans hbv1, P2.2.1.trans hib1, P2.2.2.1.trans hbm1, P1, fun l r2 hl hu => ?_,
      fun l r2 hl hu => ?_, P3, ⟨fl2, by rw [P4, hρ1]⟩, fun k w he => P5 k w (hent1 k w he)⟩
    · obtain ⟨hlv, r1', hr1', hu1, hpg1⟩ := P2.2.2.2 l r2 hl hu
      rw [hpg1]
      apply rb_mem_drop_succ keys i key Hk _ (hpk1 l r1' hr1' hu1)
      intro he; apply hlv
      have h7 := (HB1.1.2.2.2.2.2.2.2.1 l r1' hr1').2.2.2.2.2.2.1
      rw [he, hv1] at h7; exact (Option.some.inj h7).symm
    · obtain ⟨-, r1', hr1', hu1, -⟩ := P2.2.2.2 l r2 hl hu
      exact hun1 l r1' hr1' hu1
  isplitr
  · iintro !> %i %key %m' ⟨%Hk, %Hm'⟩ HP
    icases HP with ⟨%B1, %st1, %ρ1, %F1, %nv, Hn, HbNN, Hv, Htxr, Hdbw, Htk, HFt, %HP1⟩
    obtain ⟨hnm1, hbv1, hib1, hbm1, HB1, hpk1, hun1, hF1, hρ1, hent1⟩ := HP1
    iexists B1, st1, ρ1, F1, nv
    iframe
    ipureintro
    refine ⟨hnm1, hbv1, hib1, hbm1, HB1, fun l r hl hu => ?_, hun1, hF1, hρ1, hent1⟩
    apply rb_mem_drop_succ keys i key Hk _ (hpk1 l r hl hu)
    intro he
    have h7 := (HB1.1.2.2.2.2.2.2.2.1 l r hl).2.2.2.2.2.2.1
    rw [he, hnm1, Hm'] at h7; cases h7
  iintro %m' HP Hnm
  icases HP with ⟨%B1, %st1, %ρ1, %F1, %nv, Hn, HbNN, Hv, Htxr, Hdbw, Htk, HFt, %HP1⟩
  obtain ⟨hnm1, hbv1, hib1, hbm1, HB1, hpk1, hun1, hF1, hρ1, hent1⟩ := HP1
  have hbal : ∀ l r, B1.ns !! l = some r → r.nv.unbalanced' = false := by
    intro l r hl
    rcases Bool.eq_false_or_eq_true r.nv.unbalanced' with hu | hu
    · have := hpk1 l r hl hu; rw [List.drop_length] at this; cases this
    · exact hu
  ihave Hnm : B1.bv.nodes' ↦$ B1.nm $$ [Hnm]
  · rw [hbv1, hnm1]; iexact Hnm
  isimp only [bktOwnNN] at HbNN
  icases HbNN with ⟨Hbv, Hib, Hbm, Hpo, Hns⟩
  isimp only [rblTx] at Htxr
  icases Htxr with ⟨Hstats, Hpages, Hpm, Hdb, Hmeta, Hm⟩
  try wp_auto
  ihave Hwand : (B1.bv.buckets' ↦$ B1.bm -∗ ownWriteTx W txl (wtxUpd T st1 bl B1)) $$
      [Hclose Hwr Hmg Hch Hwf Hv Hnm Hbv Hib Hpo Hns Hstats Hpages Hpm Hdb Hmeta Hm]
  · iintro Hbm
    ihave Hb : bktOwn W bl B1 $$ [Hbv Hib Hnm Hbm Hpo Hns]
    · unfold bktOwn; iframe
    iapply Hclose $$ %st1 %B1 %(⟨HB1.1, by rw [hbv1]; exact Htx, hbm1⟩) [Hwr Hmg Hch Hwf Hstats Hpages Hdb
      Hmeta] Hm Hpm Hb Hv
    unfold TxW_rest_root
    simp only
    try rw [hdb]
    iframe
    ipureintro; exact Hnn
  ihave Hsh := Hshc $$ %st1 %B1 %(⟨HB1.2.1, hbv1, hib1, hbm1, hent1⟩) Htk
  have Hrel1 := rblTxRel_upd W T st1 bl B B1 HB hbv1 hib1 hbm1 hun1 hent1
  have HOK1 := rblTxOK_upd W _ T st1 bl B1 HOK HB1
  have hbal1 : bktBal (wtxUpd T st1 bl B1) bl := by
    intro B' h l r hl
    change (<[bl := B1]> T.bs) !! bl = some B' at h
    rw [GMap.lookup_insert] at h; cases h; exact hbal l r hl
  try wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (keys : List GoString) (i : Nat) (m' : GMap GoString Loc) =>
      iprop(⌜m' = B1.bm⌝ ∗ ∃ (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8)) (cv : Loc),
        child_ptr ↦ cv ∗ (B1.bv.buckets' ↦$ B1.bm -∗ ownWriteTx W txl T') ∗ txShapeR γ W T' ∗
        dbWR I γd W txl txid ρ' ∗ pgToks γ F' ∗
        ⌜rblTxOK W (uint.nat T.mv.pgid') T' ∧ rblTxRel W T T' ∧ bktBal T' bl ∧
          (∀ (k : Nat) name c, k < i → keys[k]? = some name → B1.bm !! name = some c →
            balancedFrom T' c) ∧
          freedOK W ρ'.fl txid F' ∧ (∃ fl, ρ' = { ρ with fl := fl })⌝)) $$ Hbm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [child Hwand Hsh Hdbw HFt]
  · isplitr
    · ipureintro; rfl
    iexists (wtxUpd T st1 bl B1), ρ1, F1, _
    iframe
    ipureintro
    exact ⟨HOK1, Hrel1, hbal1, fun k _ _ hk => absurd hk (Nat.not_lt_zero _), hF1, hρ1⟩
  isplitr
  · iintro !> %i %key %c %m' ⟨%Hk, %Hc⟩ ⟨%Hmm, HP⟩ Hbm
    subst Hmm
    icases HP with ⟨%T2, %ρ2, %F2, %cv, Hchild, Hwand, Hsh, Hdbw, HFt, %HQ⟩
    obtain ⟨HOK2, Hrel2, Hbal2, Hdone2, HF2, ⟨fl2, Hρ2⟩⟩ := HQ
    ihave Hown := Hwand $$ Hbm
    try wp_auto
    have hc2 : (T2.bs !! c).isSome := by
      rw [Hrel2.1.2.2.2.1 c]; exact Hkids key c (by rw [← hbm1]; exact Hc)
    have hmv2 : T2.mv = T.mv := Hrel2.1.1
    wp_apply IH $$ %I %γd %γ %W %txl %txid %ρ2 %T2 %F2 %c [] [Hown Hsh Hdbw HFt]
      as ⟨%T3, %ρ3, %F3, Hown, Hsh, Hdbw, HFt, %Hpost⟩
    · ipureintro; exact ⟨hFree, hc2, by rw [hmv2]; exact Hmtx, by rw [hmv2]; exact HOK2, HF2⟩
    · iframe
    try wp_auto
    obtain ⟨P1, P2, P3, P4, ⟨fl3, P5⟩⟩ := Hpost
    rw [hmv2] at P1
    have Hrel3 := rblTxRel_trans W T T2 T3 Hrel2 P2
    obtain ⟨B3, hB3, hbv3, -, hbm3⟩ := rblTxRel_at W T T3 Hrel3 bl B HB
    icases ownWriteTx_bm W txl T3 bl B1 B3 hB3 (hbv3.trans hbv1.symm) (hbm3.trans hbm1.symm) $$ Hown
      with ⟨Hbm, Hwand⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists B1.bm
    iframe Hbm
    isplitr
    · ipureintro; rfl
    iexists T3, ρ3, F3, c
    iframe
    ipureintro
    refine ⟨P1, Hrel3, bktBal_rel W T2 T3 P2 bl Hbal2, fun k name c' hk hkn hc' => ?_, P4,
      ⟨fl3, by rw [P5, Hρ2]⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact balancedFrom_rel W T2 T3 P2 c' (Hdone2 k name c' hk hkn hc')
    · subst hk; rw [Hk] at hkn; cases hkn; rw [Hc] at hc'; cases hc'; exact P3
  isplitr
  · iintro !> %i %key %m' ⟨%Hk, %Hm'⟩ ⟨%Hmm, -⟩
    subst Hmm
    have := (Hkset key).1 (List.mem_of_getElem? Hk)
    rw [Hm'] at this; cases this
  iintro %m' ⟨%Hmm, HP⟩ Hbm
  subst Hmm
  icases HP with ⟨%T2, %ρ2, %F2, %cv, Hchild, Hwand, Hsh, Hdbw, HFt, %HQ⟩
  obtain ⟨HOK2, Hrel2, Hbal2, Hdone2, HF2, Hρ2⟩ := HQ
  ihave Hown := Hwand $$ Hbm
  try wp_auto
  iapply HΦ
  iexists T2, ρ2, F2
  iframe
  ipureintro
  refine ⟨HOK2, Hrel2, ?_, HF2, Hρ2⟩
  intro d hr C hC l r hl
  rcases bktReach_split T2 bl d hr with rfl | ⟨Bx, name, c, hBx, hn, hrc⟩
  · exact Hbal2 C hC l r hl
  · obtain ⟨B3, hB3, -, -, hbm3⟩ := rblTxRel_at W T T2 Hrel2 bl B HB
    rw [hB3] at hBx; cases hBx
    have hn' : B1.bm !! name = some c := by rw [hbm1, ← hbm3]; exact hn
    obtain ⟨k, hk, hkn⟩ := List.getElem_of_mem ((Hkset name).2 (by rw [hn']; rfl))
    exact Hdone2 k name c hk (by rw [List.getElem?_eq_getElem hk, hkn]) hn' d hrc C hC l r hl


theorem Bucket.rebalance.wp_sproof (hnr : node.rebalance.sspec (GF := GF) (hG := hG)) :
    Bucket.rebalance.sspec (GF := GF) (hG := hG) := by
  intro I γd γ W txl txid ρ T F bl H1 H2 H3 H4 H5
  have H := rebalB_loeb hnr
  unfold rebalBw at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %I %γd %γ %W %txl %txid %ρ %T %F %bl [] [HP] HΦ
  · ipureintro; exact ⟨H1, H2, H3, H4, H5⟩
  · iexact HP

end proof

end bbolt
end EtcdGrove
end Perennial
