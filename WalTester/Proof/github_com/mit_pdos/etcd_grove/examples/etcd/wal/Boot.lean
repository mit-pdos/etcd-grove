/-
`Boot.wp_proof` (W4c U5, eleventh session). Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Boot
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.loadOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.freshOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.newRnd
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__resume
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Exist
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateFresh
public import Spec.go_uber_org.zap.NewNop
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.StepLive
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.BootAu
public import Perennial.GooseLang.NotCrashed
import Batteries.Tactic.PermuteGoals

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]
variable [wal_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem Boot.wp_proof
    (wp_nop : zap.NewNop.spec (GF := GF))
    (wp_newRnd : newRnd.spec (GF := GF) (hG := hG))
    (wp_load : loadOracle.spec (GF := GF) (hG := hG))
    (wp_exist : ∀ W : WalGS GF, wal.Exist.spec (W := W) walCodec walRaftMr)
    (wp_create : ∀ W : WalGS GF, wal.Create.specFresh (W := W) (walRaftP (GF := GF)) walRaftMr)
    (wp_fresh : freshOracle.spec (GF := GF) (hG := hG))
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_resume : member.resume.spec (GF := GF) (hG := hG))
    (wp_restart : member.restart.spec (GF := GF) (hG := hG))
    (wp_step : member.step.spec (GF := GF) (hG := hG))
    (wp_choose : rnd.choose.spec (GF := GF) (hG := hG))
    (wp_close : member.close.spec (GF := GF) (hG := hG)) :
    Boot.spec (GF := GF) (hG := hG) := by
  intro W e γ o od seed nOps hf hpath hr hfs
  have hpfW : PathFits (tWalDir e.area) := hfs.2.2
  obtain ⟨hia, hnm, hca, hdl⟩ := hpath
  wp_start as ⟨Hrun⟩
  iunfold TRun at Hrun
  icases Hrun with ⟨#Hinv, Ho, Hwo, #Harea, #Hdd, Hres, Htok, #Hdi, Hh, Hperm⟩
  iunfold tPerm at Hperm
  icases Hperm with ⟨Hperm, Hor⟩
  ihave ⟨#Hos, #Hsi⟩ := walAreaOk_os W e $$ Harea
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, -, #Hzpkg, #Hwpkg, -, -, -⟩
  -- the oracle's relation, the WAL's view raised to named when `created` (B2)
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  ihave Hrel : |={⊤}=> notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ ∃ od' : Option WalDur,
      tOrOwn γ o none ∗ tWalOwn γ od' ∗ tRelI (W := W) e.area o od' ∗
      ⌜o.created = true → ∃ d, od' = some d ∧ d.named = true⌝ $$ [Hnc Ho Hwo]
  · cases hcr : o.created with
    | true =>
      imod tInv_named W e γ o od hcr $$ [Hinv Harea Hnc Ho Hwo] with
        ⟨Hnc, Ho, %d, %c, Hwo, %hdc, #Hsl, #Hnm⟩
      · iframe; iframe #
      obtain ⟨hn, hc, hok, hw⟩ := hdc
      imodintro
      iframe Hnc
      iexists some d
      iframe Ho Hwo
      isplitl
      · iunfold tRelI
        simp only [hcr, ↓reduceIte]
        iexists d, c
        iframe #
        ipureintro; exact ⟨rfl, hc, hok, hw⟩
      · ipureintro; intro _; exact ⟨d, rfl, hn⟩
    | false =>
      imod tInv_rel W e γ o od ⊤ CoPset.subseteq_top $$ [Hinv Ho Hwo] with ⟨Ho, Hwo, #HR⟩
      · iframe; iframe #
      imodintro
      iframe Hnc
      iexists od
      iframe Ho Hwo HR
      ipureintro; intro h; cases h
  imod Hrel with ⟨Hnc, %od1, Ho, Hwo, #HR, %hnamed⟩
  imodintro
  iframe Hnc
  clear od
  wp_auto
  wp_apply wp_nop as %lg #Hzap
  wp_apply wp_newRnd as %r ⟨%rv, Hrv⟩
  try wp_auto
  ihave %hmn := typedPointsto_not_null _ _ _ $$ «$r0»
  icases typedPointsto_split _ _ _ $$ «$r0» with Hm
  simp only [TypedPointsto.typedPointstoDef]
  icases Hm with ⟨Hlg, Hr, Hop, Hwd, Hw, Hov, Ht, Hv, Hc, Hb, Hl, Htm, -⟩
  rw [show (e.orDir ++ go!"/state" : GoString) = tOrPath e.orDir from rfl]
  wp_apply (wp_load W e γ o (1 : Qp) hf) $$ [Hh Hor Ho] as %v ⟨Hh, Hor, Hrep, Ho⟩
  · iframe; iframe #
  imod osPathS_root e.R e.area e.jr (DFrac.own 1) hr (by simp) $$ Hsi with Hpath
  icases osPathS_callKey e.R e.area _ e.jr $$ Hpath with ⟨Hpath, %hkc⟩
  have hkw : callKey e.R (tWalDir e.area) = callKey e.R e.area := by rw [tWalDir_child]; exact hkc _
  ihave Hperm := osCallPerm_congr 1 hkw $$ Hperm
  try wp_auto
  rw [show (e.area ++ go!"/wal" : GoString) = tWalDir e.area from rfl]
  wp_apply (wp_exist W e.R e.jr e.area (tWalDir e.area) go!"wal" 1
      (fun od' => iprop(⌜od' = od1⌝ ∗ tWalOwn γ od1)) 0 hia hnm) $$ [Hpath Hres Hperm Htok Hwo]
    as %b ⟨Hpath, Hres, Hperm, Htok, %od2, ⟨%hod, Hwo⟩, %hb, -⟩
  · iframe; iframe #
    iapply tInv_dirAu W e γ od1
    iframe; iframe #
  subst hod
  cases b
  -- no WAL found
  have hex := hb rfl
  iunfold oracleRep at Hrep
  icases Hrep with ⟨%Hf, Hcs, #Hsince, Hscap, #Hops, Hopcap⟩
  obtain ⟨hvc, hvs, hvh⟩ := Hf
  try wp_auto
  cases hvcr : v.created'
  pick_goal 2
  · -- the oracle says `Create` returned: the view is named, which `Exist`'s `false` arm excludes
    exfalso
    obtain ⟨d, hd, hn⟩ := hnamed (by rw [← hvc, hvcr])
    subst hd
    rcases hex with h | ⟨d', h, -, hn'⟩
    · cases h
    · cases h; rw [hn] at hn'; cases hn'
  have hcr : o.created = false := by rw [← hvc, hvcr]
  iunfold tRelI at HR
  simp only [hcr, Bool.false_eq_true, ↓reduceIte]
  icases HR with %hpre
  try wp_auto
  wp_apply wp_string_to_bytes (go!"m" : GoString) as %mp ⟨Hmp, -⟩
  ihave %hmpl := ownSlice_len $$ Hmp
  ipersist Hmp
  have hmp : mp ≠ slice.nil := by
    intro h; subst h; have h1 := hmpl.1; exact absurd h1 (by rw [show sint.nat slice.nil.len = 0 from rfl]; decide)
  wp_apply (wp_create W lg e.R e.jr e.area (tWalDir e.area) go!"wal" mp go!"m" 1
      (iprop(tOrOwn γ o none ∗ tWalOwn γ (some (walDurFresh go!"m")))) 0 hia hnm hdl hca hmp (by decide)
      (by decide) walRaftMr_createOk hfs) $$ [Hpath Hres Hperm Htok Ho Hwo]
    as %w %err ⟨Hpath, Hres, Hcr⟩
  · iframe; iframe #
    iapply tInv_createAu W e γ o od2 go!"m" hex hpre.1 hcr
    iframe; iframe #
  icases Hcr with (⟨%herr, ⟨Ho, Hwo⟩, Hwf, #Hnm, #Hlen, #Hsl, Hpw, Hph⟩ | ⟨%herr, -⟩ | ⟨%herr, -⟩)
  pick_goal 2
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
      try wp_auto
      simp only [StatusDown]
      wp_auto
      iapply HΦ; itrivial
  pick_goal 2
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
      try wp_auto
      simp only [StatusDown]
      wp_auto
      iapply HΦ; itrivial
  subst herr
  try wp_auto
  wp_apply wp_fresh as %vf Hfr
  try wp_auto
  iunfold oracleRep at Hfr
  icases Hfr with ⟨%Hff, Hfcs, #Hfsince, Hfscap, #Hfops, Hfopcap⟩
  obtain ⟨-, hfs, hfh⟩ := Hff
  ihave Hrep1 : oracleRep (oracle.mk true vf.cands' vf.since' vf.synced' vf.lastHS' vf.opens') tFreshC
    $$ [Hfcs Hfscap Hfopcap]
  · iunfold oracleRep
    isplitr
    · ipureintro; exact ⟨rfl, hfs, hfh⟩
    dsimp only [tFreshC]
    iframe
    isplitl []
    · iexact Hfsince
    · iexact Hfops
  ihave #Hrel1 : tRelI (W := W) e.area tFreshC (some (walDurFresh go!"m")) $$ []
  · iunfold tRelI
    simp only [tFreshC, ↓reduceIte]
    iexists walDurFresh go!"m", tCand0
    isplitr
    · ipureintro; exact ⟨rfl, tFreshC_cand, tCandOk_freshC _, tCheckWf_freshC⟩
    rw [show tCandMark { tFreshOracle with created := true } tCand0 = 0 from rfl]
    iframe #
  wp_apply (wp_store W e γ _ o tFreshC (some (walDurFresh go!"m")) 1 hf tOrSmall_freshC)
    $$ [Hh Hor Hrep1 Ho Hwo] as ⟨Hh, Hor, Hrep1, Ho, Hwo⟩
  · iframe; iframe #
  try wp_auto
  ihave #Hc0 : contentsRep (zero_val contents) tC0 $$ []
  · iunfold contentsRep
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    rw [show (zero_val contents).ents' = slice.nil from rfl, show tC0.ents = [] from rfl]
    iapply ownSlice_nil
  wp_apply (wp_resume «$r0_ptr» (zero_val contents) tC0 _ _ _ _ _ _) $$ [Ht Hv Hc Hb Hl Htm]
    as ⟨Ht, Hv, Hc, Hb, Hl, %tm', Htm, HM⟩
  · iframe; iframe #
  try wp_auto
  ihave Hph : tPerm (GF := GF) e (1 : Qp).half $$ [Hph Hor]
  · iunfold tPerm; rw [hkw]; iframe
  ihave Hlive := memLive_intro W e γ «$r0_ptr» w _ tFreshC tFreshC tCand0 (walDurFresh go!"m") (1 : Qp).half
    _ _ _ _ _ tm' _ r rv (tMemOk_freshC _) (tMemHs_freshC _) tMemFields_c0 tCheckWf_freshC tMemSim_freshC
    $$ [Hh Hph Hop Hw Hov Hrep1 Ho Hwo Hwf Hpw Ht Hv Hc Hb Hl Htm HM Hr Hrv]
  · iframe
    isplitl [Hh Hph Hop Hw Hov Hrep1 Ho Hwo Hwf]
    · iunfold memSaveRes
      rw [show tCandMark tFreshC tCand0 = 0 from rfl, show (walDurFresh go!"m").H.length = 0 from rfl]
      iframe; iframe #
    · iunfold memFields; iframe
  have hsm : tOrSmall tFreshC := tOrSmall_freshC
  generalize tFreshC = o' at hsm ⊢
  pick_goal 2
  -- a WAL found: the restart
  try wp_auto
  ihave ⟨%cd, %hcd, #HrW⟩ := tRelI_relW W e.area o od2 $$ HR
  obtain ⟨hcd, hok, hcwf⟩ := hcd
  ihave Hperm : tPerm (GF := GF) e 1 $$ [Hperm Hor]
  · iunfold tPerm; rw [hkw]; iframe
  wp_apply (wp_restart W e γ «$r0_ptr» lg null v o cd od2 1 _ _ _ _ _ _ r rv hmn hf
      ⟨hia, hnm, hca, hdl⟩ hpfW hcd hok hcwf)
    $$ [Hh Hperm Hpath Hres Htok Hlg Hwd Hop Hw Hov Ht Hv Hc Hb Hl Htm Hr Hrv Hrep Ho Hwo]
    as %ok Hpost
  · iframe; iframe #
  icases Hpost with ⟨Hpath, Hres, Hlg, Hwd, Hpost⟩
  cases ok
  · try wp_auto
    simp only [StatusDown]
    wp_auto
    iapply HΦ; itrivial
  simp only [↓reduceIte]
  icases Hpost with ⟨%o', %ho', Hlive⟩
  have hsm : tOrSmall o' := ho'.2
  try wp_auto
  -- both starts leave the running member: the steps, then perhaps `close`
  all_goals
    ihave HI : (∃ (j : w64) (o1 : TOracle),
        "i" ∷ i_ptr ↦ j ∗ "Hlive" ∷ memLive W e γ «$r0_ptr» (1 : Qp).half o1 ∗ "%hsm1" ∷ ⌜tOrSmall o1⌝ ∗
        "Hlg" ∷ «$r0_ptr».[member, go!"lg"] ↦ lg ∗
        "Hwd" ∷ «$r0_ptr».[member, go!"walDir"] ↦ tWalDir e.area ∗
        "Hpath" ∷ osPathS e.R e.area (DFrac.own 1) e.jr ∗ "Hres" ∷ WalFs.walAreaRes (W := W) e.jr : IProp GF)
      $$ [i Hlive Hlg Hwd Hpath Hres]
    · iexists W64 0, o'
      simp only [named]
      iframe
      ipureintro; exact hsm
    wp_for HI
    wp_if_destruct
    · wp_apply (wp_step W e γ «$r0_ptr» lg o1 1 hmn hf ⟨hia, hnm, hca, hdl⟩ hpfW) $$ [Hlive Hlg Hwd Hpath Hres]
        as %b Hpost
      · iframe; iframe #
      icases Hpost with ⟨Hpath, Hres, Hlg, Hwd, Hpost⟩
      cases b
      · try wp_auto
        simp only [StatusDown]
        wp_auto
        wp_for_post
        iapply HΦ; itrivial
      simp only [↓reduceIte]
      icases Hpost with ⟨%o2, Hlive, %hsm2⟩
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, o2
      simp only [named]
      iframe
      ipureintro; exact hsm2
    -- perhaps `close`
    iunfold memLive at Hlive
    icases Hlive with ⟨%w1, %v1, %os1, %c1, %d1, %t1, %vo1, %cm1, %bs1, %l1, %tm1, %M1, %r1, %rv1, Hres1,
      Ht1, Hv1, Hc1, Hb1, Hl1, Htm1, HM1, Hr1, Hrv1, Hpw1, %Hfacts⟩
    obtain ⟨hok1, -, -, hwf1, -⟩ := Hfacts
    try wp_auto
    wp_apply wp_choose $$ [$Hrv1] as %k ⟨-, %hk⟩
    try wp_auto
    wp_if_destruct
    · iunfold memSaveRes at Hres1
      icases Hres1 with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, Hrep1, H11, H12, #H13, H14, #H15, -, -⟩
      have hsyn : tOrSmall (tSynced o1) := by unfold tOrSmall; rw [tEncodeOracle_synced]; exact hsm1
      wp_apply (wp_close W e γ «$r0_ptr» w1 v1 o1 os1 c1 d1 _ hf hok1 hsyn hwf1)
        $$ [H5 H6 H7 H8 H9 Hrep1 H11 H12 H14 Hpw1] as %b -
      · iframe; iframe #
      cases b
      · try wp_auto
        simp only [StatusDown]
        wp_auto
        iapply HΦ; itrivial
      · try wp_auto
        simp only [StatusRan]
        wp_auto
        iapply HΦ; itrivial
    · try wp_auto
      simp only [StatusRan]
      wp_auto
      iapply HΦ; itrivial

end proof

end etcd_wal
end EtcdGrove
end Perennial
