/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordRead.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the coordinator's read path (`HandleRead2Reply`, ...).
-/
module

public import Dsverify.Proof.gryff.H1.Coord
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


attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffCoordinator.HandleRead2Reply.wp_proof (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (m : model.Read2ReplyM) (gt : src.gryffproto.Tag) (rep : w32)
    (hstep : model.stepR k s (.msg (.read2Reply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) }}
      (App (App (App (coordM co go!"HandleRead2Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #gt)) (Val #rep))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  have hcase := stepRead2Reply_inv k s s' m outs hstep
  simp only [coordM]
  wp_start as ⟨Hc, Hic, HC⟩
  unfold icoordOk
  simp only [specT]
  icases Hic with ⟨-, -, -, -, #HCR, -, -, #HPr, #HSt, -, -, -⟩
  icases (coordOwn_open ρ co ic k s).1 $$ Hc with
    ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, #Hfix, Hmisc, %Hrk, Hr, Hw, Ho⟩
  icases (coordFix_open co ic k ropsR wopsR orR mtR fkR arS).1 $$ Hfix with ⟨#F1, #F2, #F3, #F4, #F5, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13, #F14⟩
  icases (amapRep_open ropsR s.rops _).1 $$ Hr with ⟨%rm, Hrm, %Hrdom, Hrents⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Hrm as Hrm
  cases hg : rm !! model.shiftInts m.requestId m.clientId with
  | none =>
    have hgm : s.rops.get? (model.shiftInts m.requestId m.clientId) = none := by
      have := Hrdom (model.shiftInts m.requestId m.clientId); rw [hg] at this
      cases h : s.rops.get? (model.shiftInts m.requestId m.clientId) with
      | none => rfl
      | some _ => rw [h] at this; cases this
    rcases hcase with ⟨-, rfl, rfl⟩ | ⟨read, hr, -⟩
    rotate_left
    · rw [hgm] at hr; cases hr
    simp only [Option.isSome_none]
    wp_auto
    wp_printf0 HPr
    iapply HΦ
    simp only [List.nil_append]
    iframe HC
    iapply (coordOwn_open ρ co ic k _).2
    iexists ropsR, wopsR, orR, mtR, fkR, arS
    iframe Hfix Hmisc Hw Ho %Hrk
    iapply (amapRep_open ropsR _ _).2
    iexists rm
    iframe Hrm Hrents
    ipureintro; exact Hrdom
  | some p =>
    icases amapEnts_take _ _ _ _ p hg $$ Hrents with ⟨Hrents, ⟨%read, %Hread, Hro⟩⟩
    icases (readOpRep_open ρ p read).1 $$ Hro with ⟨%g, %op, %rws, %w, %gd, #Hwr, Hp, #Hdep, Hop, Hmx, Hrv, Hrws, Hrwc, %Hgf⟩
    obtain ⟨Hrid, Hcid, Hkey, HN, H1, H2, H3, H4, H5, Hrws⟩ := Hgf
    rcases hcase with ⟨hn, -⟩ | ⟨read', hr', hcase⟩
    · rw [hn] at Hread; cases Hread
    rw [Hread] at hr'; cases hr'
    simp only [Option.isSome_some]
    wp_auto
    wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
    subst Hst'
    wp_apply StatsMap.IncrementStrInt.wp' $$ [Hstats] as %_ -
    · stats_key
    · iframe Hstats
    simp only [Option.getD_some]
    wp_auto
    have h2 : BitVec.sdiv (W64 3) (W64 2) + W64 1 = model.NHALF + 1 := by decide
    rw [H2, h2] at *
    wp_if_destruct
    · rcases hcase with ⟨-, rv, hrv, rfl, rfl⟩ | ⟨hq, -⟩
      rotate_left
      · exfalso; simp only [model.sge, model.sle, _root_.decide_eq_false_iff_not] at hq
        exact hq Hif
      wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
      subst Hst'
      wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
      · stats_key
      · iframe Hstats
      rw [Hkey]
      wp_auto
      wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
      subst Hst'
      wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
      · stats_key
      · iframe Hstats
      icases (amapRep_open orR s.ongoingReqs _).1 $$ Ho with ⟨%om, Hom, %Hodom, Hoents⟩
      wp_apply wp_mapDelete $$ Hom as Hom
      wp_apply wp_mapDelete $$ Hrm as Hrm
      unfold optVtRep
      rw [hrv]
      dsimp only
      icases Hrv with ⟨%gv, #Hgv, %Hgvrv⟩
      iStructNamedPrefix Hgv "gv"
      wp_auto
      rw [Hrid, Hcid]
      have hv : rv.v = gv.V' := by rw [← Hgvrv]; rfl
      rw [hv, List.singleton_append] at *
      wp_apply HCR $$ %read.requestId %read.clientId %gv.V' %s.storeVT %o %w [HC]
        as %_ ⟨%_, HC⟩
      · iframe HC Hwr
      iclear Hp Hop Hmx Hrws
      iapply HΦ
      simp only [model.RState.storeVT]
      iframe HC
      iapply (coordOwn_open ρ co ic k _).2
      iexists ropsR, wopsR, orR, mtR, fkR, arS
      dsimp only
      iframe Hfix Hmisc Hw
      rw [HN]
      isplitl []
      · ipureintro; exact ropsKeyed_del _ _ Hrk -- H1b-R1
      isplitl [Hrm Hrents]
      · iapply (amapRep_open ropsR _ _).2
        iexists (GMap.delete (model.shiftInts m.requestId m.clientId) rm)
        iframe Hrm
        isplitl []
        · ipureintro; intro key
          by_cases hk : key = model.shiftInts m.requestId m.clientId
          · subst hk; rw [GMap.lookup_delete, amap_del_get_self]; rfl
          · rw [GMap.lookup_delete_ne _ (Ne.symm hk), amap_del_get_ne _ _ _ hk]; exact Hrdom key
        iapply amapEnts_del $$ Hrents
      · iapply (amapRep_open orR _ _).2
        iexists (GMap.delete read.n om)
        iframe Hom
        isplitl []
        · ipureintro; intro key
          by_cases hk : key = read.n
          · subst hk; rw [GMap.lookup_delete, amap_del_get_self]; rfl
          · rw [GMap.lookup_delete_ne _ (Ne.symm hk), amap_del_get_ne _ _ _ hk]; exact Hodom key
        iapply amapEnts_drop $$ Hoents
    · rcases hcase with ⟨hq, -⟩ | ⟨-, rfl, rfl⟩
      · exfalso; simp only [model.sge, model.sle, _root_.decide_eq_true_eq] at hq
        exact Hif hq
      iapply HΦ
      simp only [model.RState.storeVT, List.nil_append]
      iframe HC
      iapply (coordOwn_open ρ co ic k _).2
      iexists ropsR, wopsR, orR, mtR, fkR, arS
      dsimp only
      iframe Hfix Hmisc Hw Ho
      isplitl []
      · ipureintro; exact ropsKeyed_put _ _ _ Hrk (by have h := Hrk _ _ Hread; exact h) -- H1b-R1
      iapply (amapRep_open ropsR _ _).2
      iexists rm
      iframe Hrm
      isplitl []
      · ipureintro; intro key
        rw [amap_put_get]
        by_cases hk : key = model.shiftInts m.requestId m.clientId
        · subst hk; rw [hg, if_pos rfl]; rfl
        · rw [if_neg hk]; exact Hrdom key
      iapply amapEnts_update _ _ _ _ p _ hg
      iframe Hrents
      iapply (readOpRep_open ρ p _).2
      iexists _, op, rws, w, gd
      iframe Hwr Hp Hdep Hop Hmx Hrv Hrws Hrwc
      ipureintro
      exact ⟨Hrid, Hcid, Hkey, HN, H1, rfl, H3, H4, H5, Hrws⟩

end

end Perennial.gryff.replica2
