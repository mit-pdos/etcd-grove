/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Write1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the participant's `HandleWrite1` (forced writes only).
-/
module

public import Dsverify.Proof.gryff.H1.Read
public import Dsverify.Proof.gryff.H1.Pure
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

theorem wp_newWriteOp (rid cid n fw : w32) (key val : w64) (d : src.gryffproto.Dep) (id : w32)
    (mat : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon }}
      (App (App (App (App (App (App (App (App (App (Val (@! src.gryffcommon.newWriteOp))
        (Val #rid)) (Val #cid)) (Val #n)) (Val #fw)) (Val #key)) (Val #val)) (Val #d)) (Val #id))
        (Val #mat))
    {{ (op : Loc), RET #op; ∃ wp : Loc,
        op ↦ (src.gryffcommon.OngoingWriteOp.mk wp false false) ∗
        wp ↦ (src.gryffproto.Write1Proxied.mk rid cid n fw key val d id mat) }} := by
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  iapply HΦ
  iexists _
  iframe


set_option hygiene false in
/-- `HandleWrite1`'s common tail: the reply, the `Max`, `SentWrite1Reply = true`, `Printf`
(leaves the `forceWrite <= 0` branch, refuted by `hfw`, as a second goal). -/
local macro "w1_prog" : tactic => `(tactic| (
  wp_apply GryffParticipant.wp_GetStoreMetadata_int $$ [Hsm Hst]
    as %md2 ⟨%tp2, %gt2, %Htag2, #Htp2, Hmd2, Hsm, Hback2, -, -⟩
  · iframe Hfix Hsm Hst
  wp_auto
  wp_if_destruct
  rotate_left
  · exfalso; simp at Hif; word
  wp_apply wp_map_len $$ Hsm as Hsm
  wp_apply HStats as %_ ⟨%st, %Hst', Hstats⟩
  subst Hst'
  wp_apply StatsMap.Max.wp' $$ [Hstats] as %_ -
  · stats_key
  · iframe Hstats
  wp_apply wp_map_lookup1 $$ How as How
  try (simp only [hc, Option.getD_some]; wp_auto)
  wp_printf HPr))

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffParticipant.wp_HandleWrite1_int (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (smR owR : Loc) (sm : GMap w64 Loc) (ow : GMap w32 Loc) (V : w64 → IProp GF)
    (vt : model.ValTag) (ong : AMap 32 w32) (val : w64) (n : w32) (dp mp : Loc)
    (gd : src.gryffproto.Dep) (gmt : src.gryffproto.Tag) (rid cid fw coord : w32)
    (hd' : (¬ ∃ r, ong.get? cid = some r ∧ model.sgt r rid = true) →
      0 ≤ sint.Z gd.Key' → gd.Key' = W64 0)
    (hfw' : (¬ ∃ r, ong.get? cid = some r ∧ model.sgt r rid = true) → 0 < sint.Z fw) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiFix pa ip k smR owR ∗ smR ↦$ sm ∗ storeRep sm vt.t ∗ owR ↦$ ow ∗ owRep ow ong ∗
        ipartiOk ip V ∗ V vt.v ∗ dp ↦□ gd ∗ mp ↦□ gmt }}
      (App (App (App (App (App (App (App (App (App (Val (pa @!! go.GoType.PointerType
        src.gryffcommon.GryffParticipant.ty @!! go!"HandleWrite1")) (Val #(W64 0))) (Val #val))
        (Val #n)) (Val #dp)) (Val #rid)) (Val #cid)) (Val #mp)) (Val #fw)) (Val #coord))
    {{ (rp : Loc), RET #rp;
        (⌜∃ r, ong.get? cid = some r ∧ model.sgt r rid = true⌝ ∗ ⌜rp = Loc.null⌝ ∗
          smR ↦$ sm ∗ storeRep sm vt.t ∗ owR ↦$ ow ∗ owRep ow ong ∗ V vt.v) ∨
        (⌜¬ ∃ r, ong.get? cid = some r ∧ model.sgt r rid = true⌝ ∗
          ∃ (sm' : GMap w64 Loc) (ow' : GMap w32 Loc) (gt : src.gryffproto.Tag),
          smR ↦$ sm' ∗ storeRep sm' (depVt vt gd).t ∗ owR ↦$ ow' ∗ owRep ow' (ongPut ong cid rid) ∗
          V (depVt vt gd).v ∗
          rp ↦ (src.gryffproto.Write1Reply.mk rid cid (rid32 k)
            (src.gryffproto.ValTag.mk (W64 (-1)) gt)) ∗ ⌜tagOf gt = (depVt vt gd).t⌝) }} := by
  wp_start as ⟨#Hfix, Hsm, Hst, How, Howr, #Hip, HV, #Hdp, #Hmp⟩
  icases (ipartiOk_open ip V).1 $$ Hip with ⟨#HGet, #HSet, #HPr, #HStats, -, -⟩
  icases (partiFix_open pa ip k smR owR).1 $$ Hfix with ⟨#Hid, #Hipf, #Hnc, #Hstp, #Howp⟩
  simp only [specT]
  iStructNamedPrefix Hdp "d"
  iStructNamedPrefix dVt "dv"
  rw [owRep_eq]
  icases Howr with ⟨%Hdom, Hents⟩
  icases owEntries_take _ _ cid $$ Hents with ⟨Hents, Hc⟩
  wp_auto
  wp_printf HPr
  wp_apply wp_map_lookup1 $$ How as How
  cases hc : ow !! cid with
  | none =>
    have hnone : ong.get? cid = none := by
      have := Hdom cid; rw [hc] at this
      cases h : ong.get? cid with
      | none => rfl
      | some _ => rw [h] at this; cases this
    have hnst : ¬ ∃ r, ong.get? cid = some r ∧ model.sgt r rid = true := by
      rintro ⟨r, hr, -⟩; rw [hnone] at hr; cases hr
    have hd := hd' hnst
    have hfw := hfw' hnst
    simp only [Option.getD_none]
    rw [show decide (zero_val Loc = null) = true from decide_eq_true rfl]
    wp_auto
    wp_join iprop(∃ sm1 : GMap w64 Loc, smR ↦$ sm1 ∗ storeRep sm1 (depVt vt gd).t ∗
        V (depVt vt gd).v ∗ dep_ptr ↦ dp ∗ r_ptr ↦ pa) with [Hsm Hst HV dep r]
        as ⟨%sm1, Hsm, Hst, HV, dep, r⟩
    · have hk0 := hd (by simpa using Hif)
      rw [hk0]
      wp_apply GryffParticipant.wp_HandleOverwrite_int $$ [$Hfix $Hsm $Hst $Hip $HV $dvT]
        as ⟨%sm', Hsm, Hst, HV, -⟩
      isplitl []
      · ipureintro; rfl
      iexists sm'
      have : depVt vt gd = ovw vt gd.Vt'.V' (tagOf gd.Vt'.T') := by
        unfold depVt; rw [if_pos (by simpa using Hif)]
      rw [this]
      iframe Hsm Hst HV dep r
    · have : depVt vt gd = vt := by
        unfold depVt; rw [if_neg (by simpa using Hif)]
      rw [this]
      iexists sm
      iframe Hsm Hst HV dep r
    wp_printf HPr
    wp_apply wp_map_lookup1 $$ How as How
    rw [hc]
    simp only [Option.getD_none]
    wp_auto
    wp_apply wp_map_lookup1 $$ How as How
    rw [hc]
    simp only [Option.getD_none]
    wp_auto
    wp_apply wp_newWriteOp as %op1 ⟨%wp1, Hop1, Hwp1⟩
    wp_apply wp_mapInsert $$ How as How
    w1_prog
    have hput : ongPut ong cid rid = ong.put cid rid := by unfold ongPut; rw [hnone]
    iapply HΦ
    iright
    isplitl []
    · ipureintro; rintro ⟨r, hr, -⟩; rw [hnone] at hr; cases hr
    iexists sm1, (<[cid := op1]> ow), gt2
    iframe Hsm How HV «$r0»
    isplitl [Hback2 Hmd2]
    · icases Hback2 $$ Hmd2 with ⟨H, -⟩
      iexact H
    rw [hput, owRep_eq]
    isplitl [Hents Hop1 Hwp1]
    · isplitl []
      · ipureintro; intro c'
        rw [amap_put_get]
        by_cases h : c' = cid
        · subst h; simp
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; simp [h, Hdom c']
      iapply owEntries_put _ _ cid rid op1
      iframe Hents
      unfold owE
      iexists _, _
      iframe Hop1 Hwp1
      ipureintro; simp
    ipureintro; exact Htag2
  | some op =>
    dsimp only
    icases Hc with ⟨%r, %Hr, Hop⟩
    unfold owE
    icases Hop with ⟨%g, %wm, Hop, Hwm, %Hg⟩
    obtain ⟨Hsent, Hfast, Hwrid, Hwcid, HwK⟩ := Hg
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hop
    simp only [Option.getD_some, decide_eq_false Hnn]
    wp_auto
    wp_apply wp_map_lookup1 $$ How as How
    simp only [hc, Option.getD_some]
    wp_auto
    rw [Hwrid]
    wp_if_destruct
    · -- a stale request: nil, nothing changed
      iapply HΦ
      ileft
      isplitl []
      · ipureintro; exact ⟨r, Hr, by simp [model.sgt, model.slt, Hif]⟩
      isplitl []
      · ipureintro; rfl
      iframe Hsm Hst How HV
      isplitl []
      · ipureintro; exact Hdom
      iapply owEntries_restore _ _ cid r op hc Hr
      iframe Hents
      unfold owE
      iexists g, wm
      iframe Hop Hwm
      ipureintro; exact ⟨Hsent, Hfast, Hwrid, Hwcid, HwK⟩
    · -- not stale
      have hns := Hif
      have hnst : ¬ ∃ r, ong.get? cid = some r ∧ model.sgt r rid = true := by
        rintro ⟨r', hr', hgt⟩; rw [Hr] at hr'; cases hr'
        simp [model.sgt, model.slt] at hgt; exact hns hgt
      have hd := hd' hnst
      have hfw := hfw' hnst
      wp_join iprop(∃ sm1 : GMap w64 Loc, smR ↦$ sm1 ∗ storeRep sm1 (depVt vt gd).t ∗
          V (depVt vt gd).v ∗ dep_ptr ↦ dp ∗ r_ptr ↦ pa) with [Hsm Hst HV dep r]
          as ⟨%sm1, Hsm, Hst, HV, dep, r⟩
      · have hk0 := hd (by simpa using Hif)
        rw [hk0]
        wp_apply GryffParticipant.wp_HandleOverwrite_int $$ [$Hfix $Hsm $Hst $Hip $HV $dvT]
          as ⟨%sm', Hsm, Hst, HV, -⟩
        isplitl []
        · ipureintro; rfl
        iexists sm'
        have : depVt vt gd = ovw vt gd.Vt'.V' (tagOf gd.Vt'.T') := by
          unfold depVt; rw [if_pos (by simpa using Hif)]
        rw [this]
        iframe Hsm Hst HV dep r
      · have : depVt vt gd = vt := by
          unfold depVt; rw [if_neg (by simpa using Hif)]
        rw [this]
        iexists sm
        iframe Hsm Hst HV dep r
      wp_printf HPr
      wp_apply wp_map_lookup1 $$ How as How
      simp only [hc, Option.getD_some, decide_eq_false Hnn]
      wp_auto
      wp_apply wp_map_lookup1 $$ How as How
      simp only [hc, Option.getD_some]
      wp_auto
      rw [Hwrid]
      wp_if_destruct
      · -- an older request of the client: a new entry
        have hlt := Hif
        wp_apply wp_newWriteOp as %op1 ⟨%wp1, Hop1, Hwp1⟩
        wp_apply wp_mapInsert $$ How as How
        w1_prog
        have hput : ongPut ong cid rid = ong.put cid rid := by
          unfold ongPut; rw [Hr]; simp [model.slt, hlt]
        iclear Hop Hwm
        iapply HΦ
        iright
        isplitl []
        · ipureintro; rintro ⟨r', hr', hgt⟩; rw [Hr] at hr'; cases hr'
          simp [model.sgt, model.slt] at hgt; exact hns hgt
        iexists sm1, (<[cid := op1]> ow), gt2
        iframe Hsm How HV «$r0»
        isplitl [Hback2 Hmd2]
        · icases Hback2 $$ Hmd2 with ⟨H, -⟩
          iexact H
        rw [hput, owRep_eq]
        isplitl [Hents Hop1 Hwp1]
        · isplitl []
          · ipureintro; intro c'
            rw [amap_put_get]
            by_cases h : c' = cid
            · subst h; simp
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; simp [h, Hdom c']
          iapply owEntries_put _ _ cid rid op1
          iframe Hents
          unfold owE
          iexists _, _
          iframe Hop1 Hwp1
          ipureintro; simp
        ipureintro; exact Htag2
      · -- the same request again: the entry stays
        have hrr : r = rid := by
          apply BitVec.toInt_inj.mp; simp only [sint.Z] at Hif hns; omega
        subst hrr
        wp_apply wp_map_lookup1 $$ How as How
        simp only [hc, Option.getD_some, decide_eq_false Hnn]
        wp_auto
        w1_prog
        have hput : ∀ c', (ongPut ong cid r).get? c' = ong.get? c' := by
          intro c'; unfold ongPut; rw [Hr]; simp [model.slt]
        iapply HΦ
        iright
        isplitl []
        · ipureintro; rintro ⟨r', hr', hgt⟩; rw [Hr] at hr'; cases hr'
          simp [model.sgt, model.slt] at hgt
        iexists sm1, ow, gt2
        iframe Hsm How HV «$r0»
        isplitl [Hback2 Hmd2]
        · icases Hback2 $$ Hmd2 with ⟨H, -⟩
          iexact H
        rw [owRep_eq]
        isplitl [Hents Hop Hwm]
        · isplitl []
          · ipureintro; intro c'; rw [hput]; exact Hdom c'
          iapply owEntries_congr _ ong _ (fun c' => (hput c').symm)
          iapply owEntries_restore _ _ cid r op hc Hr
          iframe Hents
          unfold owE
          iexists _, wm
          iframe Hop Hwm
          ipureintro; simp [Hfast, Hwrid, Hwcid, HwK]
        ipureintro; exact Htag2

end

end Perennial.gryff.replica2
