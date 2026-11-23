/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordWrite.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the coordinator's `StartWrite`.
-/
module

public import Dsverify.Proof.gryff.H1.CoordStartDefs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

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
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5

theorem wp_map_make1_tagmap :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make1 [go.GoType.MapType src.gryffproto.Tag.ty
        (go.GoType.SliceType go.int32)])) (Val #()))
    {{ (mref : Loc), RET #mref; True }} := by
  wp_start
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_alloc_untyped (PairV #(zero_val GoSlice) (ArrayV (List.map map.entryV []))) (by simp)) as %l -
  iapply HΦ
  itrivial

theorem wp_newWrite (rid cid : w32) (key v : w64) (dp : Loc) (n : w32) (mt : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon }}
      (App (App (App (App (App (App (App (Val (@! src.gryffcommon.newWrite))
        (Val #rid)) (Val #cid)) (Val #key)) (Val #v)) (Val #dp)) (Val #n)) (Val #mt))
    {{ (wp : Loc), RET #wp; ∃ (g : src.gryffcommon.WriteOp), wp ↦ g ∗
        g.Op' ↦ (src.gryffcommon.Op.mk rid cid key dp) ∗
        g.maxValTag' ↦ (src.gryffproto.ValTag.mk (W64 (-1)) (src.gryffproto.Tag.mk (W32 0) (W32 0) (W32 0))) ∗
        ⌜g.N' = n ∧ g.WriteValue' = v ∧ g.MaxAppliedTag' = mt ∧ g.WriteTag' = Loc.null ∧
          g.numWrite1Applies' = W64 0 ∧ g.numWrite1Replies' = W64 0 ∧
          g.numWrite2Applies' = W64 0 ∧ g.numWrite2Replies' = W64 0 ∧
          g.sentWrite2Round' = false ∧ g.startedShortcircuitTimeout' = false⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_NewOp as %o Ho
  wp_apply wp_map_make1_tagmap as %mref -
  iapply HΦ
  iexists _
  iframe
  ipureintro; simp

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffCoordinator.StartWrite.wp_proof (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (rid cid : w32) (v : w64) (dp w : Loc) (gd : src.gryffproto.Dep)
    (hid : s.id = rid32 k)
    (hstep : model.stepR k s (.write rid cid 0 v (depOf gd)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ dp ↦□ gd ∗ writerIs ρ cid w }}
      (App (App (App (App (App (coordM co go!"StartWrite") (Val #rid)) (Val #cid))
        (Val #(W64 0))) (Val #v)) (Val #dp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  simp only [model.stepR] at hstep
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ :=
    stepClientWrite_inv s s' rid cid v (depOf gd) outs hstep
  have hW : (s.maxN + 1 : w32) = s.maxN + W32 1 := rfl
  rw [hW] at hs1 hs3 hs4
  simp only [coordM]
  wp_start as ⟨Hc, Hic, HC, #Hdp, #Hwr⟩
  unfold icoordOk
  simp only [specT]
  icases Hic with ⟨-, -, #HS1, -, -, -, -, #HPr, #HSt, -, -, -⟩
  icases (coordOwn_open ρ co ic k s).1 $$ Hc with
    ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, #Hfix, Hmisc, %Hrk, Hr, Hw, Ho⟩
  icases (coordFix_open co ic k ropsR wopsR orR mtR fkR arS).1 $$ Hfix with ⟨#F1, #F2, #F3, #F4, #F5, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13, #F14⟩
  unfold coordMisc
  icases Hmisc with ⟨%mst, %mat, %fkc, %mt, %fk, Hn, Hs, Ha, Hf, Hmt, Hfk, %Hmt0, Hmtm, Hfkc, %Hsrt⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Hfk as Hfk
  wp_join iprop(∃ fw : w32, forceWrite_ptr ↦ fw) with [forceWrite] as ⟨%fw, forceWrite⟩
  wp_apply wp_slice_make2 (V := w32) as %cw ⟨Hcw, -⟩
  · ipureintro; decide
  wp_apply wp_map_lookup2 $$ Hmt as Hmt
  wp_join iprop(∃ (tp : Loc) (mt' : GMap w64 Loc), tag_ptr ↦ tp ∗ mtR ↦$ mt' ∗
      c_ptr ↦ co ∗ key_ptr ↦ W64 0 ∗
      ⌜mt' !! W64 0 = some tp ∧ ∀ kk, kk ≠ W64 0 → mt' !! kk = none⌝ ∗
      (⌜tp = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
        ∃ gt : src.gryffproto.Tag, tp ↦□ gt)) with [tag Hmt Hmtm c key] as
      ⟨%tp, %mt', tag, Hmt, c, key, ⟨%Hmt1, %Hmt2⟩, #Htp⟩
  · obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.mp Hif
    rw [hp0]
    simp only [Option.getD_some]
    iexists p0, mt
    iframe tag Hmt Hmtm c key
    ipureintro; exact ⟨hp0, Hmt0⟩
  · have hn : mt !! W64 0 = none := by simpa using Hif
    iclear Hmtm
    wp_apply wp_mapInsert $$ Hmt as Hmt
    wp_join_done
    iexists _, _
    iframe tag Hmt c key
    isplitl []
    · ipureintro
      refine ⟨GMap.lookup_insert _ _ _, fun kk hk => ?_⟩
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact Hmt0 kk hk
    ileft; ipureintro; rfl
  wp_printf HPr
  wp_apply wp_newWrite as %wp0 ⟨%gw, Hwp, Hwop, Hmvt, %Hgw⟩
  wp_apply wp_ShiftInts
  icases (amapRep_open wopsR s.wops _).1 $$ Hw with ⟨%wm, Hwm, %Hwdom, Hwents⟩
  wp_apply wp_mapInsert $$ Hwm as Hwm
  wp_apply wp_slice_make2 (V := w32) as %rsl -
  · ipureintro; decide
  wp_apply wp_newOngoingOp as %op ⟨%gop, Hop, Hsr, Hsrc, Hsw, %Hgop⟩
  icases (amapRep_open orR s.ongoingReqs _).1 $$ Ho with ⟨%om, Hom, %Hodom, Hoents⟩
  wp_apply wp_mapInsert $$ Hom as Hom
  have hsend : sendsTo [W32 0, W32 1, W32 2]
      (.write1 (write1Msg k (⟨rid, cid, s.maxN + W32 1, v, depOf gd, ⟨-1, model.tag0⟩, 0, 0, 0, 0,
        false, none⟩ : WriteOp))) = some outs := by
    rw [hid] at hs6; exact hs6
  ihave HS := HS1 $$ %co %wp0 %_ %mat %arS %_ %s.storeVT %outs %o %hsend
  ipersist Hmvt
  obtain ⟨Hg1, Hg2, Hg3, Hg4, Hg5, Hg6, Hg7, Hg8, Hg9, Hg10⟩ := Hgw
  wp_apply HS $$ [HC Hwp Hwop Hmvt Ha] as %_ ⟨%_, HC, Hwo, Ha⟩
  · iframe HC Ha F9
    iapply (writeOpRep_open ρ co wp0 _).2
    iexists _, _, w, gd
    iframe Hwr Hwp Hwop Hdp
    isplitl []
    · rw [Hg3]; iexact Htp
    isplitl []
    · unfold optVtRep
      iexists _
      iframe Hmvt
      ipureintro; rfl
    isplitl []
    · dsimp only; ipureintro; exact Hg4
    ipureintro
    simp [Hg1, Hg2, Hg5, Hg6, Hg7, Hg8, Hg9, Hg10]
  wp_printf HPr
  iapply HΦ
  rw [hs5]
  iframe HC
  iapply (coordOwn_open ρ co ic k s').2
  iexists ropsR, wopsR, orR, mtR, fkR, arS
  iframe Hfix
  rw [hs1, hs2, hs3, hs4]
  isplitl [Hn Hs Ha Hf Hmt Hfk Hfkc]
  · unfold coordMisc
    iexists mst, mat, fkc, mt', fk
    iframe Hn Hs Ha Hf Hmt Hfk Hfkc
    isplitl []
    · ipureintro; exact Hmt2
    isplitl [Htp]
    · rw [Hmt1]
      iexact Htp
    ipureintro; exact wops_sorted_put _ _ _ Hsrt -- H1-R10
  iframe Hr %Hrk
  isplitl [Hwm Hwents Hwo]
  · iapply (amapRep_open wopsR _ _).2
    iexists _
    iframe Hwm
    isplitl []
    · ipureintro; intro key
      rw [amap_put_get]
      by_cases hk : key = model.shiftInts rid cid
      · subst hk; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk]; exact Hwdom key
    iapply amapEnts_put
    iframe Hwo
    iapply amapEnts_forget $$ Hwents
  iapply (amapRep_open orR _ _).2
  iexists _
  iframe Hom
  isplitl []
  · ipureintro; intro key
    rw [amap_put_get]
    by_cases hk : key = s.maxN + W32 1
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk]; exact Hodom key
  iapply amapEnts_put
  isplitl [Hoents]
  · iapply amapEnts_forget $$ Hoents
  iapply ongoingOpRep_close
  unfold ongoingOpRepC
  iexists gop, []
  iframe Hop Hsr Hsrc Hsw
  ipureintro; simp [Hgop]

end

end Perennial.gryff.replica2
