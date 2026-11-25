/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordStart.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the coordinator's `StartRead`.
-/

module

public import Dsverify.Proof.gryff.H1.CoordStartDefs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Replica2.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffCoordinator.StartRead.wp_proof (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3)
    (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (rid cid : w32) (dp w : Loc) (gd : src.gryffproto.Dep)
    (hid : s.id = rid32 k)
    (hstep : model.stepR k s (.read rid cid 0 (depOf gd)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ dp ↦□ gd ∗ writerIs ρ cid w }}
      (App (App (App (App (coordM co go!"StartRead") (Val #rid)) (Val #cid)) (Val #(W64 0)))
        (Val #dp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  simp only [coordM]
  wp_start as ⟨Hc, Hic, HC, #Hdp, #Hwr⟩
  unfold icoordOk
  simp only [specT]
  icases Hic with ⟨#HS1, -, -, -, -, -, -, #HPr, #HSt, -, -, -⟩
  icases (coordOwn_open ρ co ic k s).1 $$ Hc with
    ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, #Hfix, Hmisc, %Hrk, Hr, Hw, Ho⟩
  icases (coordFix_open co ic k ropsR wopsR orR mtR fkR arS).1 $$ Hfix with ⟨#F1, #F2, #F3, #F4, #F5, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13, #F14⟩
  unfold coordMisc
  icases Hmisc with ⟨%mst, %mat, %fkc, %mt, %fk, Hn, Hs, Ha, Hf, Hmt, Hfk, %Hmt0, Hmtm, Hfkc, %Hsrt⟩
  have hnd : (s.wops.map Prod.fst).Nodup := wops_sorted_nodup s.wops Hsrt -- H1-R10
  simp only [model.stepR] at hstep
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := stepClientRead_inv s s' rid cid (depOf gd) outs hstep
  have hW : (s.maxN + 1 : w32) = s.maxN + W32 1 := rfl
  rw [hW] at hs1 hs2 hs5 hs6
  wp_auto
  wp_apply wp_slice_make2 (V := w32) as %rsl -
  · ipureintro; decide
  wp_apply wp_newOngoingOp as %op ⟨%gop, Hop, Hsr, Hsrc, Hsw, %Hgop⟩
  icases (amapRep_open orR s.ongoingReqs _).1 $$ Ho with ⟨%om, Hom, %Hodom, Hoents⟩
  wp_apply wp_mapInsert $$ Hom as Hom
  wp_apply wp_newRead as %rp ⟨%grd, Hrp, Hrop, %Hgrd⟩
  icases (amapRep_open ropsR s.rops _).1 $$ Hr with ⟨%rm, Hrm, %Hrdom, Hrents⟩
  try wp_auto
  wp_apply wp_ShiftInts
  wp_apply wp_mapInsert $$ Hrm as Hrm
  icases (amapRep_open wopsR s.wops _).1 $$ Hw with ⟨%wm, Hwm, %Hwdom, Hwents⟩
  ihave Hoents := amapEnts_forget _ _ _ (s.maxN + W32 1) $$ Hoents
  ihave Hoents := amapEnts_put _ _ _ (s.maxN + W32 1) op
    ({ requestId := rid, clientId := cid, isRead := true, shortReads := [] } : OngoingOp) $$ [Hoents Hop Hsr Hsrc Hsw]
  · iframe Hoents
    iapply ongoingOpRep_close
    unfold ongoingOpRepC
    iexists gop, []
    iframe Hop Hsr Hsrc Hsw
    ipureintro; simp [Hgop]
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  wp_func_lits
  have hdom1 : ∀ j, ((<[s.maxN + W32 1 := op]> om) !! j).isSome =
      ((s.ongoingReqs.put (s.maxN + W32 1)
        { requestId := rid, clientId := cid, isRead := true, shortReads := [] }).get? j).isSome := by
    intro j
    rw [amap_put_get]
    by_cases hj : j = s.maxN + W32 1
    · subst hj; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hj), if_neg hj]; exact Hodom j
  iapply (wp_map_for_range (fun keys i => iprop(∃ (orx : AMap 32 OngoingOp) (wv : Loc),
      ⌜0 ≤ i ∧ rdChar (s.maxN + W32 1) (s.ongoingReqs.put (s.maxN + W32 1)
          { requestId := rid, clientId := cid, isRead := true, shortReads := [] }) orx
        ((keys.take i.toNat).filterMap (fun kk => AMap.get? s.wops kk))⌝ ∗
      wop_ptr ↦ wv ∗ c_ptr ↦ co ∗ key_ptr ↦ W64 0 ∗ n_ptr ↦ s.maxN + W32 1 ∗
      requestId_ptr ↦ rid ∗ clientId_ptr ↦ cid ∗
      orR ↦$ <[s.maxN + W32 1 := op]>om ∗ amapEnts orx (<[s.maxN + W32 1 := op]>om) ongoingOpRep ∗
      amapEnts s.wops wm (fun p w => writeOpRep ρ co p w)))) $$ Hwm
  iintro %keys %hkeys
  isplitl [wop c key n requestId clientId Hom Hoents Hwents]
  · iexists _, _
    iframe wop c key n requestId clientId Hom Hoents Hwents
    ipureintro; exact ⟨by omega, by simpa using rdChar_nil _ _⟩
  isplitl []
  · imodintro
    iintro %i %key %p ⟨%hk1, %hk2⟩ ⟨%orx, %wv, ⟨%Hi0, %Hchar⟩, Hwop, Hc, Hkey, Hnp, Hrq, Hcl, Hom, Hoents, Hwents⟩
    icases amapEnts_acc _ _ _ key p hk2 $$ Hwents with ⟨⟨%w0, %Hw0, Hw0⟩, Hwback⟩
    icases (writeOpRep_open ρ co p w0).1 $$ Hw0 with
      ⟨%g, %o0, %wr, %gd0, #Hwrr, Hp, Hgo, #Hgd, Hmat, Hmvt, Hwt, %Hgw⟩
    obtain ⟨Ho1, Ho2, Ho3, Ho4, Ho5, Ho6, Ho7, Ho8, Ho9, Ho10, Ho11, Ho12, Ho13⟩ := Hgw
    have htake : (keys.take (i + 1).toNat).filterMap (fun kk => AMap.get? s.wops kk) =
        (keys.take i.toNat).filterMap (fun kk => AMap.get? s.wops kk) ++ [w0] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_succ, hk1]
      simp [Hw0]
    have hwmem : w0 ∈ s.wops.map Prod.snd := by
      unfold AMap.get? at Hw0
      obtain ⟨l1, l2, hl, -⟩ := List.lookup_eq_some_iff.mp Hw0
      exact List.mem_map.mpr ⟨(key, w0), by rw [hl]; simp, rfl⟩
    wp_auto
    rw [show decide (o0.Key' = W64 0) = true by simp [Ho3]]
    wp_auto
    rw [Ho12]
    cases hsent : w0.sentWrite2Round
    · wp_auto
      wp_printf HPr
      have hpres := hs6 w0 hwmem hsent
      have hpx : (orx.get? w0.n).isSome := by
        rw [rdChar_isSome _ _ _ _ Hchar]; exact hpres
      obtain ⟨p', hp'⟩ : ∃ p', (<[s.maxN + W32 1 := op]> om) !! w0.n = some p' := by
        have := hdom1 w0.n
        rw [hpres] at this
        exact Option.isSome_iff_exists.mp this
      wp_apply wp_map_lookup1 $$ Hom as Hom
      rw [Ho4]
      have hp2 : (if s.maxN + W32 1 = w0.n then some op else om !! w0.n) = some p' := hp'
      rw [hp2]
      simp only [Option.getD_some]
      icases amapEnts_take _ _ _ w0.n p' hp' $$ Hoents with ⟨Hoents, ⟨%ox, %Hox, Hox⟩⟩
      icases ongoingOpRep_open p' ox $$ Hox with ⟨%gq, %sw, Hgp, Hsr, Hcap, Hsw, %Hgq⟩
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w32) (t := go.int32) [s.maxN + W32 1]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w32) _ _ _ [s.maxN + W32 1] (DFrac.own 1) $$ [$Hsr $Hcap $Hsl]
        as %r ⟨Hr, Hrcap, -⟩
      wp_apply wp_map_lookup1 $$ Hom as Hom
      rw [Ho4, hp2]
      simp only [Option.getD_some]
      wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitl []
      · ipureintro; rfl
      iexists orx.put w0.n { ox with shortReads := ox.shortReads ++ [s.maxN + W32 1] }, p
      iframe Hwop Hc Hkey Hnp Hrq Hcl Hom
      isplitl []
      · ipureintro
        refine ⟨by omega, ?_⟩
        rw [htake]; exact rdChar_step _ _ _ _ _ ox Hchar hsent Hox
      isplitl [Hoents Hgp Hr Hrcap Hsw]
      · iapply amapEnts_update _ _ _ w0.n p' _ hp'
        iframe Hoents
        iapply ongoingOpRep_close
        unfold ongoingOpRepC
        iexists _, sw
        iframe Hgp Hr Hrcap Hsw
        ipureintro; exact Hgq
      iapply Hwback
      iexists w0
      isplitl []
      · ipureintro; exact Hw0
      iapply (writeOpRep_open ρ co p w0).2
      iexists g, o0, wr, gd0
      iframe Hwrr Hp Hgo Hgd Hmat Hmvt Hwt
      ipureintro
      exact ⟨Ho1, Ho2, Ho3, Ho4, Ho5, Ho6, Ho7, Ho8, Ho9, Ho10, Ho11, Ho12, Ho13⟩
    · wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitl []
      · ipureintro; rfl
      iexists orx, p
      iframe Hwop Hc Hkey Hnp Hrq Hcl Hom Hoents
      isplitl []
      · ipureintro
        refine ⟨by omega, ?_⟩
        rw [htake]; exact rdChar_sent _ _ _ _ _ Hchar hsent
      iapply Hwback
      iexists w0
      isplitl []
      · ipureintro; exact Hw0
      iapply (writeOpRep_open ρ co p w0).2
      iexists g, o0, wr, gd0
      iframe Hwrr Hp Hgo Hgd Hmat Hmvt Hwt
      ipureintro
      exact ⟨Ho1, Ho2, Ho3, Ho4, Ho5, Ho6, Ho7, Ho8, Ho9, Ho10, Ho11, Ho12, Ho13⟩
  iintro ⟨%orx, %wv, ⟨%Hi0, %Hchar⟩, Hwop, Hc, Hkey, Hnp, Hrq, Hcl, Hom, Hoents, Hwents⟩ Hwm
  have hfin : ∀ j, orx.get? j = s'.ongoingReqs.get? j := by
    obtain ⟨hk1, hk2, hk3⟩ := hkeys
    rw [show (↑wm.size : Int).toNat = keys.length by omega, List.take_length] at Hchar
    have hp := keys_perm s.wops hnd keys (fun kk => by rw [hk1 kk, Hwdom kk]) hk3
    have h1 := rdChar_perm _ _ _ _ _ hp Hchar
    intro j; rw [h1 j, hs5 j]
  wp_auto
  wp_apply wp_slice_make2 (V := w32) as %rsl0 ⟨Hrsl, Hrcap⟩
  · ipureintro; decide
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ihave HI : (∃ (iv : w32) (rsl : GoSlice), "i" ∷ i_ptr ↦ iv ∗ "replicas" ∷ replicas_ptr ↦ rsl ∗
      "Hrsl" ∷ rsl ↦* replAfter (rid32 k) iv ∗ "Hrcap" ∷ ownSliceCap w32 rsl (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ 3⌝ : IProp GF) $$ [i replicas Hrsl Hrcap]
  · iexists W32 0, rsl0
    rw [show replAfter (rid32 k) (W32 0) = [] from rfl]
    iframe i replicas Hrsl Hrcap
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · have hc : sint.Z iv < 3 := by word
    by_cases hik : iv = rid32 k
    · rw [show decide (iv = rid32 k) = true by simpa using hik]
      wp_auto
      wp_for_post
      iframe
      iexists iv + W32 1, rsl
      iframe
      rw [replAfter_succ _ _ Hi.1 hc, if_pos hik, List.append_nil]
      iframe
      ipureintro; word
    · rw [show decide (iv = rid32 k) = false by simpa using hik]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w32) (t := go.int32) [iv]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w32) _ _ _ [iv] (DFrac.own 1) $$ [$Hrsl $Hrcap $Hsl]
        as %r2 ⟨Hr2, Hr2cap, -⟩
      wp_for_post
      iframe
      iexists iv + W32 1, r2
      iframe
      rw [replAfter_succ _ _ Hi.1 hc, if_neg hik]
      iframe
      ipureintro; word
  have hi3 : iv = W32 3 := by word
  subst hi3
  rw [replAfter_three]
  have hsend : sendsTo (([0, 1, 2] : List w32).filter (fun x => x ≠ rid32 k))
      (.read1 (read1Msg k (⟨rid, cid, s.maxN + W32 1, none, none, 1, 0, 0, false, false, []⟩ :
        ReadOp) s.storeVT)) = some outs := by
    rw [← hs7, mapM_sendPeer_filter, hid]
    rfl
  ihave HS := HS1 $$ %rp %_ %rsl %_ %s.storeVT %outs %o %hsend
  ihave Hnil := ownSlice_nil (V := w32) (DFrac.own 1)
  wp_apply HS $$ [HC Hrp Hrop Hrsl Hnil] as %_ ⟨%_, HC, Hro, -⟩
  · iframe HC Hrsl
    iapply (readOpRep_open ρ rp _).2
    iexists _, _, [], w, gd
    iframe Hwr Hrp Hrop Hdp
    obtain ⟨Hg1, Hg2, Hg3, Hg4, Hg5, Hg6, Hg7, Hg8, Hg9⟩ := Hgrd
    rw [Hg9]
    iframe Hnil
    unfold optVtRep
    simp only [Hg2, Hg3]
    isplitr
    · ipureintro; trivial
    isplitr
    · ipureintro; trivial
    isplitr
    · iapply ownSliceCap_nil -- H1-R11
    ipureintro
    simp [Hg1, Hg5, Hg6, Hg7, Hg8]
  iapply HΦ
  rw [hs4]
  iframe HC
  iapply (coordOwn_open ρ co ic k s').2
  iexists ropsR, wopsR, orR, mtR, fkR, arS
  iframe Hfix
  rw [hs1, hs3, hs2]
  isplitl [Hn Hs Ha Hf Hmt Hfk Hmtm Hfkc]
  · unfold coordMisc
    iexists mst, mat, fkc, mt, fk
    iframe Hn Hs Ha Hf Hmt Hfk Hmtm Hfkc
    ipureintro; exact ⟨Hmt0, Hsrt⟩
  isplitl []
  · ipureintro; exact ropsKeyed_put _ _ _ Hrk rfl -- H1b-R1
  isplitl [Hrm Hrents Hro]
  · iapply (amapRep_open ropsR _ _).2
    iexists _
    iframe Hrm
    isplitl []
    · ipureintro; intro key
      rw [amap_put_get]
      by_cases hk : key = model.shiftInts rid cid
      · subst hk; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk]; exact Hrdom key
    iapply amapEnts_put
    iframe Hro
    iapply amapEnts_forget $$ Hrents
  isplitl [Hwm Hwents]
  · iapply (amapRep_open wopsR _ _).2
    iexists wm
    iframe Hwm Hwents
    ipureintro; exact Hwdom
  iapply (amapRep_open orR _ _).2
  iexists _
  iframe Hom
  isplitl []
  · ipureintro; intro j
    rw [hdom1 j, ← rdChar_isSome _ _ _ _ hs5 j]
  iapply amapEnts_congr _ _ _ _ hfin $$ Hoents

end

end Perennial.gryff.replica2
