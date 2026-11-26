/- Lean-first (no Rocq counterpart). The proof of `member.opOwnSnap`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opOwnSnap
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__saveSnap
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.copyOps
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.nameBound
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReleaseLockTo
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OwnSnapAu
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OwnSnapPurge
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.purgeRound
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.CandsLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section pure
variable [GooseExts]

/-- The candidates after `k` turns of the raise loop. -/
def tRaisePre (o : TOracle) (a : w64) (k : Nat) : List TCand :=
  (o.cands.take k).map (tRaiseCand o a) ++ o.cands.drop k

theorem tRaisePre_zero (o : TOracle) (a : w64) : tRaisePre o a 0 = o.cands := by simp [tRaisePre]

theorem tRaisePre_all (o : TOracle) (a : w64) {k : Nat} (hk : o.cands.length ≤ k) :
    tRaisePre o a k = (tRaiseNames o a).cands := by
  simp [tRaisePre, tRaiseNames, List.take_of_length_le hk, List.drop_of_length_le hk]

theorem tRaisePre_get (o : TOracle) (a : w64) {k : Nat} {cd : TCand} (hk : o.cands[k]? = some cd) :
    (tRaisePre o a k)[k]? = some cd := by
  have hl : k < o.cands.length := (List.getElem?_eq_some_iff.1 hk).1
  unfold tRaisePre
  rw [List.getElem?_append_right (by simp; omega)]
  simp [hk, show k - min k o.cands.length = 0 by omega]

theorem tRaisePre_set (o : TOracle) (a : w64) {k : Nat} {cd : TCand} (hk : o.cands[k]? = some cd) :
    (tRaisePre o a k).set k (tRaiseCand o a cd) = tRaisePre o a (k + 1) := by
  have hl : k < o.cands.length := (List.getElem?_eq_some_iff.1 hk).1
  unfold tRaisePre
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_set]
  by_cases hn : n = k
  · subst hn
    rw [if_pos rfl]
    have : n < ((o.cands.take n).map (tRaiseCand o a) ++ o.cands.drop n).length := by simp; omega
    rw [if_pos this, List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_take, hk]
  · rw [if_neg (Ne.symm hn)]
    by_cases hlt : n < k
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
      simp [List.getElem?_take, hlt, show n < k + 1 by omega]
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_take, List.getElem?_drop]
      congr 1; omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

set_option maxHeartbeats 2000000 in
theorem member.opOwnSnap.wp_proof (wp_choose : rnd.choose.spec (GF := GF) (hG := hG))
    (wp_saveSnap : member.saveSnap.spec (GF := GF) (hG := hG))
    (wp_copyOps : copyOps.spec (GF := GF) (hG := hG))
    (wp_nameBound : nameBound.spec (GF := GF) (hG := hG))
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_Release : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.specR (W := W) (Sio := ioNone) (walRaftP (GF := GF))
        walRaftMr)
    (wp_purge : purgeRound.spec (GF := GF) (hG := hG)) :
    member.opOwnSnap.spec (GF := GF) (hG := hG) := by
  intro W e γ m lg qc o hf hroom
  wp_start as ⟨Hlive, Hlg, Hwdir⟩
  iunfold memLive at Hlive
  icases Hlive with ⟨%w, %v, %os, %c, %d, %t, %vo, %cm, %bs, %l, %tm, %M, %r, %rv, Hres, Ht, Hv, Hc, Hb,
    Hl, Htm, HM, Hr, Hrv, Hpw, %Hfacts⟩
  obtain ⟨hok, hhs, hfl, hwf, hms⟩ := Hfacts
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe Hlg Hwdir
    simp only [↓reduceIte]
    iexists o
    isplitl
    · iunfold memLive
      iexists w, v, os, c, d, t, vo, cm, bs, l, tm, M, r, rv
      iframe
      ipureintro; exact ⟨hok, hhs, hfl, hwf, hms⟩
    · ipureintro; omega
  wp_apply wp_choose $$ [$Hrv] as %k ⟨⟨%rv1, Hrv⟩, %hk⟩
  rw [if_neg (by word)] at hk
  have ha1 : uint.nat bs < uint.nat (bs + W64 1 + k) := by word
  have ha2 : uint.nat (bs + W64 1 + k) ≤ uint.nat cm := by word
  have hl63 := tMemSim_last_lt hms hok.2.2.2.2.2.2.2.2.1
  have hcl := tMemSim_commitLe hms
  have ha63 : uint.nat (bs + W64 1 + k) < 2 ^ 63 := by omega
  try wp_auto
  wp_apply (wp_map_lookup1 (K := w64) (V := w64) go.uint64 go.uint64 tm M (bs + W64 1 + k) (DFrac.own 1)) $$ [$HM] as HM
  have hta : uint.nat ((M !! (bs + W64 1 + k)).getD (zero_val w64)) < 2 ^ 63 := by
    cases hM : M !! (bs + W64 1 + k) with
    | none => show uint.nat (W64 0) < 2 ^ 63; decide
    | some x => exact hfl.2 _ _ hM
  have hsim := tMemSim_own (t := (M !! (bs + W64 1 + k)).getD (zero_val w64)) hms ha1 ha2
  ihave ⟨Hres, #Hpers⟩ := memSaveRes_pers W e γ m w v o os c d qc $$ Hres
  wp_apply (wp_saveSnap W e γ m w v o os c d qc (bs + W64 1 + k) ((M !! (bs + W64 1 + k)).getD (zero_val w64))
    hf hok hhs ha63 hta (tOrRoom_snap hroom (Nat.le_refl _) _ _) hsim.1 hwf) $$ [$Hres] as %b1 Hpost1
  cases b1
  · try wp_auto
    iapply HΦ
    iframe Hlg Hwdir
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  try wp_auto
  ihave Hres1 := memSaveRes_postOp W e γ m w _ c qc $$ [$Hpers $Hpost1]
  icases Hres1 with ⟨%v1, %os1, %d1, Hres1, %Hok1⟩
  generalize hA : bs + W64 1 + k = a at *
  generalize hT : (M !! a).getD (zero_val w64) = ta at *
  obtain ⟨hok1, hhs1⟩ := Hok1
  have hsn1 : tOrSmall (tSnapO1 o a ta) := tOrRoom_snap hroom (Nat.le_refl _) a ta
  have hcw1 := tCheckWf_snapO hwf ha63 hta hsn1
  iunfold memSaveRes at Hres1
  icases Hres1 with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, Hrep, H11, H12, #H13, H14, #H15, #H16, #H17⟩
  iunfold oracleRep at Hrep
  icases Hrep with ⟨%Hof, Hcands, #Hsince, Hsincecap, #Hopens, Hopenscap⟩
  iunfold candsOwn at Hcands
  icases Hcands with ⟨%cvs, Hcs, Hcscap, #Hcel⟩
  ihave %Hcslen := ownSlice_len $$ Hcs
  ihave Hsince2 := Hsince
  iunfold opsRep at Hsince2
  icases Hsince2 with ⟨%svs, #Hsv, #Hsvel⟩
  ihave %Hsvl := ownSlice_len $$ Hsv
  ihave %Hsvel_len := opsElems_length $$ Hsvel
  ihave HI : (∃ (ci : w64) (vs' : List cand),
      "ci" ∷ ci_ptr ↦ ci ∗ "Hcs" ∷ v1.cands' ↦* vs' ∗
      "Hel" ∷ candsElems vs' (tRaisePre (tSnapO o a ta) a (sint.nat ci)) ∗
      "%Hci" ∷ ⌜0 ≤ sint.Z ci ∧ sint.Z ci ≤ sint.Z v1.cands'.len ∧ vs'.length = cvs.length⌝ : IProp GF)
      $$ [ci Hcs]
  · iexists W64 0, cvs
    rw [show sint.nat (W64 0) = 0 from rfl, tRaisePre_zero]
    iframe
    isplitl []
    · iexact Hcel
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HI
  icases Hel with #Hel
  ihave %Hel_len := candsElems_length $$ Hel
  have hrl : (tRaisePre (tSnapO o a ta) a (sint.nat ci)).length = (tSnapO o a ta).cands.length := by
    simp [tRaisePre]; omega
  by_cases hlt : sint.Z ci < sint.Z v1.cands'.len
  · rw [if_pos (by simp [hlt])]
    have hil : sint.nat ci < vs'.length := by
      have : sint.nat ci < sint.nat v1.cands'.len := by word
      omega
    obtain ⟨cv, Hcv⟩ : ∃ cv, vs'[sint.nat ci]? = some cv := ⟨_, List.getElem?_eq_getElem hil⟩
    have hil2 : sint.nat ci < (tSnapO o a ta).cands.length := by omega
    obtain ⟨cd, Hcd⟩ : ∃ cd, (tSnapO o a ta).cands[sint.nat ci]? = some cd :=
      ⟨_, List.getElem?_eq_getElem hil2⟩
    icases candsElems_lookup vs' _ (sint.nat ci) cv Hcv $$ Hel with ⟨%cd', %Hcd', #Hcdr⟩
    rw [tRaisePre_get _ a Hcd] at Hcd'
    cases Hcd'
    iunfold candRep at Hcdr
    icases Hcdr with ⟨%Hcdf, #Hcdh⟩
    have hb : 0 ≤ sint.Z ci ∧ sint.Z ci < sint.Z v1.cands'.len := ⟨Hci.1, hlt⟩
    icases ownSlice_elem_acc (sint.Z ci) cv v1.cands' (DFrac.own 1) vs' Hci.1
      (by simpa [sint.nat] using Hcv) $$ Hcs with ⟨Hcv, Hcsback⟩
    wp_auto
    iterate 4 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    wp_apply (wp_copyOps cv.h' cd.h) as %hs ⟨%hvs, Hh, Hhcap, #Hhel⟩
    · iexact Hcdh
    ihave HI2 : (∃ (i : w64) (hs' : GoSlice) (hvs' : List walOp),
        "i" ∷ i_ptr ↦ i ∗ "h" ∷ h_ptr ↦ hs' ∗ "Hh" ∷ hs' ↦* hvs' ∗
        "Hhcap" ∷ ownSliceCap walOp hs' (DFrac.own 1) ∗
        "Hhel" ∷ opsElems hvs' (cd.h ++ (tSnapO o a ta).since.take (sint.nat i)) ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v1.since'.len⌝ : IProp GF) $$ [i h Hh Hhcap]
    · iexists W64 0, hs, hvs
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp only [List.take_zero, List.append_nil]
      iframe
      isplitl []
      · iexact Hhel
      ipureintro; constructor <;> word
    wp_for HI2
    icases Hhel with #Hhel
    by_cases hlt2 : sint.Z i < sint.Z v1.since'.len
    · rw [if_pos (by simp [hlt2])]
      have hil' : sint.nat i < svs.length := by
        have : sint.nat i < sint.nat v1.since'.len := by word
        omega
      obtain ⟨sv, Hsvi⟩ : ∃ sv, svs[sint.nat i]? = some sv := ⟨_, List.getElem?_eq_getElem hil'⟩
      have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z v1.since'.len := ⟨Hi.1, hlt2⟩
      icases ownSlice_elem_acc (sint.Z i) sv v1.since' DFrac.discard svs Hi.1
        (by simpa [sint.nat] using Hsvi) $$ Hsv with ⟨Hsvv, -⟩
      icases opsElems_lookup svs (tSnapO o a ta).since (sint.nat i) sv Hsvi $$ Hsvel with ⟨%op, %Hop, #Hopr⟩
      wp_auto
      iterate 4 (try simp only [hb2, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_apply wp_slice_append $$ [$Hh $Hhcap $Hosl] as %hs2 ⟨Hh2, Hhcap2, -⟩
      ihave Hhel2 := opsElems_snoc hvs' _ sv op $$ [$Hhel $Hopr]
      wp_for_post
      iframe
      iexists i + W64 1, hs2, (hvs' ++ [sv])
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hi1, List.take_add_one, Hop]
      simp only [Option.toList_some, List.append_assoc]
      iframe
      ipureintro; constructor <;> word
    · simp only [hlt2, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hin2 : sint.nat i = (tSnapO o a ta).since.length := by
        have : sint.nat i = sint.nat v1.since'.len := by word
        omega
      have hH : cd.h ++ List.take (sint.nat i) (tSnapO o a ta).since = tCandHist (tSnapO o a ta) cd := by
        rw [hin2, List.take_length]; rfl
      rw [hH]
      wp_auto
      imod ownSlice_persist $$ Hh with #Hh
      wp_apply (wp_nameBound hs' (tCandHist (tSnapO o a ta) cd) a)
      · iunfold opsRep; iexists hvs'; isplitl []
        · iexact Hh
        · iexact Hhel
      try wp_auto
      iterate 4 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      have hcvu : cv.unl' = cd.unl := Hcdf.1
      have hci1 : sint.nat (ci + W64 1) = sint.nat ci + 1 := by word
      wp_if_destruct
      · iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
        wp_for_post
        ihave Hcs := Hcsback $$ Hcv
        iframe
        iexists ci + W64 1, _
        iframe
        rw [hci1, ← tRaisePre_set _ a Hcd]
        isplitl []
        · iapply candsElems_set
          isplitl []
          · iexact Hel
          iunfold candRep
          isplitr
          · ipureintro
            simp only [tRaiseCand]
            rw [if_pos (by rw [← hcvu]; word)]
            exact ⟨rfl, Hcdf.2⟩
          · rw [tRaiseCand_h]; iexact Hcdh
        ipureintro
        refine ⟨by word, by word, by rw [List.length_set]; exact Hci.2.2⟩
      · wp_for_post
        ihave Hcs := Hcsback $$ Hcv
        have hset : vs'.set (sint.Z ci).toNat cv = vs' := by
          apply List.ext_getElem?
          intro n
          rw [List.getElem?_set]
          split
          · rename_i hn
            subst hn
            exact Hcv.symm
          · rfl
        rw [hset]
        iframe
        iexists ci + W64 1, vs'
        iframe
        rw [hci1, ← tRaisePre_set _ a Hcd]
        have hrc : tRaiseCand (tSnapO o a ta) a cd = cd := by
          simp only [tRaiseCand]
          rw [if_neg (by rw [← hcvu]; word)]
        rw [hrc]
        have hset2 : (tRaisePre (tSnapO o a ta) a (sint.nat ci)).set (sint.nat ci) cd =
            tRaisePre (tSnapO o a ta) a (sint.nat ci) := by
          have hg := tRaisePre_get (tSnapO o a ta) a Hcd
          obtain ⟨hlt3, heq⟩ := List.getElem?_eq_some_iff.1 hg
          conv => lhs; rw [← heq]
          exact List.set_getElem_self hlt3
        rw [hset2]
        isplitl []
        · iexact Hel
        ipureintro
        refine ⟨by word, by word, Hci.2.2⟩
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hcin : sint.nat ci = (tSnapO o a ta).cands.length := by
      have : sint.nat ci = sint.nat v1.cands'.len := by word
      omega
    have hl1 : (tSnapO1 o a ta).since.length < 2 ^ 64 := by have := tOrSmall_since_lt hsn1; omega
    have hlenH : (tCandHist (tSnapO o a ta) c).length < 2 ^ 64 := by
      have := (hcw1.2 c hok1.2.1).2; omega
    have hok2 := tMemOk_release hok1 a hlenH
    have hok3 := tMemOk_raise hok1 a
    have hsm' : tOrSmall (tRaiseNames (tSnapO o a ta) a) := by
      unfold tOrSmall; rw [tRaiseNames_length, tEncodeOracle_snapO]; unfold tOrRoom at hroom; omega
    wp_auto
    ihave Hrep : oracleRep v1 (tRaiseNames (tSnapO o a ta) a) $$ [Hcs Hcscap Hsincecap Hopenscap]
    · iunfold oracleRep
      isplitr
      · ipureintro; exact Hof
      iframe
      isplitl
      · iunfold candsOwn; iexists vs'; iframe
        rw [← tRaisePre_all _ a (k := sint.nat ci) (by omega)]; iexact Hel
      · simp only [tRaiseNames]; iframe #
    ihave #Hrel : tRelI (W := W) e.area (tRaiseNames (tSnapO o a ta) a) (some d1) $$ [H16 H15]
    · iunfold tRelI
      simp only [show (tRaiseNames (tSnapO o a ta) a).created = true from hok1.1, ↓reduceIte]
      iexists d1, tRaiseCand (tSnapO o a ta) a c
      isplitr
      · ipureintro; exact ⟨rfl, tRaiseNames_mem a hok1.2.1, tMemOk_candOk0 hok3, tCheckWf_raise hcw1 a⟩
      isplitl
      · rw [tRaiseNames_mark]; iexact H16
      · iexact H15
    iunfold tPerm at H6
    icases H6 with ⟨Hpw_, H6⟩
    wp_apply (wp_store W e γ v1 os1 (tRaiseNames (tSnapO o a ta) a) (some d1) 1 hf hsm')
      $$ [H5 H6 Hrep H11 H12] as ⟨H5, H6, Hrep, H11, H12⟩
    · iframe; iframe #
    ihave H6 : tPerm (GF := GF) e qc $$ [Hpw_ H6]
    · iunfold tPerm; iframe
    try wp_auto
    have hlh : tCandHist (tSnapO o a ta) c = tCandHist o c ++ [tSnapOp a ta] := tSnapO_hist o c a ta
    have hmark1 : tCandMark (tSnapO o a ta) c = (tCandHist o c).length + 1 := by
      unfold tSnapO; rw [tSynced_mark _ c hl1, tSnapO1_hist']; simp
    have hH1 : d1.H[(tCandHist o c).length]? = some (WalOpG.snap (absSnapMd a ta) true) := by
      have h4 : d1.H.map WalOpG.toM = (tCandHist (tSnapO o a ta) c).map absOp := hok1.2.2.2.1
      rw [hlh, List.map_append] at h4
      have h5 := congrArg (fun L => L[(tCandHist o c).length]?) h4
      simp only [List.getElem?_map] at h5
      rw [List.getElem?_append_right (by simp)] at h5
      simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero, List.getElem?_map] at h5
      cases hx : d1.H[(tCandHist o c).length]? with
      | none => rw [hx] at h5; cases h5
      | some x =>
        rw [hx] at h5
        cases x with
        | snap m al => simp only [Option.map_some, Option.some.injEq] at h5; cases h5; rfl
        | save h es => simp [WalOpG.toM, absOp, tSnapOp] at h5
    ihave Hau := tInv_releaseAu W e γ (tRaiseNames (tSnapO o a ta) a) (tRaiseCand (tSnapO o a ta) a c) d1 a ta
      (tCandHist o c).length (tCandMark (tSnapO o a ta) c) ⟨[W64 1], [], [], [], false⟩ hok1.1
      (tRaiseNames_mem a hok1.2.1) (tMemOk_candOk0 hok2) hH1 (by omega) $$ [H12 H11]
    · iframe
      iframe H3 H15
      rw [tRaiseNames_mark]; iexact H16
    -- the member's handle, shared for the call (the tester assumes nothing of I/O errors: `ioNone`) and
    -- taken back after it
    iapply fupd_wp
    imod walOpenWS_alloc (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) ⊤ 0 $$ [H14]
      with ⟨%γs, H14, %hγ0⟩
    · iapply walHdl_of_wf (W := W) ioNone _ _ _ _ 0 walCov_ioNone $$ H14
    rcases γs with ⟨γs1, γs2, γsi⟩; dsimp only at hγ0; subst hγ0
    let γs : WalShN := ⟨γs1, γs2, 0⟩
    imodintro
    wp_apply (lc := 1) (wp_Release W e.R e.jr e.area w (tWalDir e.area) γs 1 a ta (tCandHist o c).length
        (tCandMark (tSnapO o a ta) c) ⟨[W64 1], [], [], [], false⟩
        (fun d' => iprop(⌜d' = d1⌝ ∗ tWalOwn γ (some (tReleaseD d1 a)) ∗
          tOrOwn γ (tRaiseNames (tSnapO o a ta) a) none))) $$ [H14 Hau]
      as %err ⟨H14, %dq, %hdq, H12, H11⟩
    · iframe; iframe #
    subst dq
    iapply fupd_wp
    imod walOpenWS_reclaim (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) γs $$ [H14 Hlc1]
      with H14
    · iframe H14 Hlc1
    imodintro
    ihave H14 := walHdl_wf (W := W) ioNone _ _ _ _ $$ H14
    cases err with
    | ok ie =>
      wp_auto
      iapply HΦ
      iframe Hlg Hwdir
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial
    | nil =>
      wp_auto
      wp_apply wp_choose $$ [$Hrv] as %k2 ⟨⟨%rv2, Hrv⟩, %hk2⟩
      rw [if_neg (by word)] at hk2
      try wp_auto
      wp_if_destruct
      · -- the purge round: every candidate's purge bound raised, the oracle stored, the round
        generalize ho2 : tRaiseNames (tSnapO o a ta) a = o2 at *
        generalize hc2 : tRaiseCand (tSnapO o a ta) a c = c2 at *
        generalize hd2 : tReleaseD d1 a = d2 at *
        have hmk2 : tCandMark o2 c2 = tCandMark (tSnapO o a ta) c := by rw [← ho2, ← hc2]; rfl
        have hH2 : d2.H = d1.H := by rw [← hd2]; rfl
        have hcw2 : tCheckWf o2 := by rw [← ho2]; exact tCheckWf_raise hcw1 a
        have hhs2 : tMemHs o2 d2 := by rw [← ho2, ← hd2]; exact tMemHs_raise hhs1 a
        have hsim2 : tMemSim o2 c2 a l cm := by rw [← ho2, ← hc2]; exact tMemSim_raise hsim.2 a
        have hlen2 : (tEncodeOracle o2).length = (tEncodeOracle o).length + 56 := by
          rw [← ho2, tRaiseNames_length, tEncodeOracle_snapO]
        iunfold oracleRep at Hrep
        icases Hrep with ⟨%Hof2, Hcands2, #Hsince2, Hsincecap2, #Hopens2, Hopenscap2⟩
        iunfold candsOwn at Hcands2
        icases Hcands2 with ⟨%cvs2, Hcs2, Hcscap2, #Hcel2⟩
        ihave %Hcslen2 := ownSlice_len $$ Hcs2
        ihave HJ : (∃ (ci : w64) (vs' : List cand),
            "ci" ∷ ci_ptr ↦ ci ∗ "Hcs" ∷ v1.cands' ↦* vs' ∗
            "Hel2" ∷ candsElems vs' (tPurPre o2 (sint.nat ci)) ∗
            "%Hci" ∷ ⌜0 ≤ sint.Z ci ∧ sint.Z ci ≤ sint.Z v1.cands'.len ∧ vs'.length = cvs2.length⌝ : IProp GF)
            $$ [ci Hcs2]
        · iexists W64 0, cvs2
          rw [show sint.nat (W64 0) = 0 from rfl, tPurPre_zero]
          iframe
          isplitl []
          · iexact Hcel2
          ipureintro; refine ⟨by word, by word, rfl⟩
        ihave %Hcs2len := candsElems_length $$ Hcel2
        wp_for HJ
        icases Hel2 with #Hel2
        ihave %Hel_len := candsElems_length $$ Hel2
        have hrl : (tPurPre o2 (sint.nat ci)).length = o2.cands.length := tPurPre_length _ _
        by_cases hlt : sint.Z ci < sint.Z v1.cands'.len
        · rw [if_pos (by simp [hlt])]
          have hil : sint.nat ci < vs'.length := by
            have : sint.nat ci < sint.nat v1.cands'.len := by word
            omega
          obtain ⟨cv, Hcv⟩ : ∃ cv, vs'[sint.nat ci]? = some cv := ⟨_, List.getElem?_eq_getElem hil⟩
          have hil2 : sint.nat ci < o2.cands.length := by omega
          obtain ⟨cd, Hcd⟩ : ∃ cd, o2.cands[sint.nat ci]? = some cd :=
            ⟨_, List.getElem?_eq_getElem hil2⟩
          icases candsElems_lookup vs' _ (sint.nat ci) cv Hcv $$ Hel2 with ⟨%cd', %Hcd', #Hcdr⟩
          rw [tPurPre_get _ Hcd] at Hcd'
          cases Hcd'
          iunfold candRep at Hcdr
          icases Hcdr with ⟨%Hcdf, #Hcdh⟩
          have hb : 0 ≤ sint.Z ci ∧ sint.Z ci < sint.Z v1.cands'.len := ⟨Hci.1, hlt⟩
          icases ownSlice_elem_acc (sint.Z ci) cv v1.cands' (DFrac.own 1) vs' Hci.1
            (by simpa [sint.nat] using Hcv) $$ Hcs with ⟨Hcv, Hcsback⟩
          have hci1 : sint.nat (ci + W64 1) = sint.nat ci + 1 := by word
          wp_auto
          iterate 4 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
          wp_if_destruct
          · iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
            wp_for_post
            ihave Hcs := Hcsback $$ Hcv
            iframe
            iexists ci + W64 1, _
            iframe
            rw [hci1, ← tPurPre_set _ Hcd]
            isplitl []
            · iapply candsElems_set
              isplitl []
              · iexact Hel2
              iunfold candRep
              isplitr
              · ipureintro
                simp only [tPurCand]
                rw [if_pos (by rw [← Hcdf.1, ← Hcdf.2]; word)]
                exact ⟨Hcdf.1, Hcdf.1⟩
              · rw [tPurCand_h]; iexact Hcdh
            ipureintro
            refine ⟨by word, by word, by rw [List.length_set]; exact Hci.2.2⟩
          · wp_for_post
            ihave Hcs := Hcsback $$ Hcv
            have hset : vs'.set (sint.Z ci).toNat cv = vs' := by
              apply List.ext_getElem?
              intro n
              rw [List.getElem?_set]
              split
              · rename_i hn
                subst hn
                exact Hcv.symm
              · rfl
            rw [hset]
            iframe
            iexists ci + W64 1, vs'
            iframe
            rw [hci1, ← tPurPre_set _ Hcd]
            have hrc : tPurCand cd = cd := by
              simp only [tPurCand]
              rw [if_neg (by rw [← Hcdf.1, ← Hcdf.2]; word)]
            rw [hrc]
            have hset2 : (tPurPre o2 (sint.nat ci)).set (sint.nat ci) cd = tPurPre o2 (sint.nat ci) := by
              have hg := tPurPre_get o2 Hcd
              obtain ⟨hlt3, heq⟩ := List.getElem?_eq_some_iff.1 hg
              conv => lhs; rw [← heq]
              exact List.set_getElem_self hlt3
            rw [hset2]
            isplitl []
            · iexact Hel2
            ipureintro
            refine ⟨by word, by word, Hci.2.2⟩
        · rw [if_neg (by simp [hlt])]
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hcin : sint.nat ci = o2.cands.length := by
            have : sint.nat ci = sint.nat v1.cands'.len := by word
            omega
          have hok4 := tMemOk_pur hok2
          have hsm4 : tOrSmall (tPurNames o2) := by
            unfold tOrSmall; rw [tPurNames_length, hlen2]; unfold tOrRoom at hroom; omega
          wp_auto
          ihave Hrep : oracleRep v1 (tPurNames o2) $$ [Hcs Hcscap2 Hsincecap2 Hopenscap2]
          · iunfold oracleRep
            isplitr
            · ipureintro; exact Hof2
            iframe
            isplitl
            · iunfold candsOwn; iexists vs'; iframe
              rw [← tPurPre_all _ (k := sint.nat ci) (by omega)]; iexact Hel2
            · simp only [tPurNames]; iframe #
          ihave #Hrel2 : tRelI (W := W) e.area (tPurNames o2) (some d2) $$ [H16 H15]
          · iunfold tRelI
            simp only [show (tPurNames o2).created = true from hok4.1, ↓reduceIte]
            iexists d2, tPurCand c2
            isplitr
            · ipureintro; exact ⟨rfl, hok4.2.1, tMemOk_candOk0 hok4, tCheckWf_pur hcw2⟩
            isplitl
            · rw [tPurNames_mark, hmk2]; iexact H16
            · iexact H15
          iunfold tPerm at H6
          icases H6 with ⟨Hpw_, H6⟩
          wp_apply (wp_store W e γ v1 o2 (tPurNames o2) (some d2) 1 hf hsm4)
            $$ [H5 H6 Hrep H11 H12] as ⟨H5, H6, Hrep, H11, H12⟩
          · iframe; iframe #
          ihave H6 : tPerm (GF := GF) e qc $$ [Hpw_ H6]
          · iunfold tPerm; iframe
          try wp_auto
          wp_apply wp_choose $$ [$Hrv] as %k3 ⟨⟨%rv3, Hrv⟩, %hk3⟩
          rw [if_neg (by word)] at hk3
          try wp_auto
          ihave #H13c := H13
          iunfold WalFs.walAreaOk at H13c
          icases H13c with ⟨#Hwinv, -⟩
          ihave #Hacc := tInv_purgeAcc W e γ (tPurNames o2) (tPurCand c2) d2.H (tPurNames_all _) $$ H3
          wp_apply (wp_purge W walRaftP walRaftMr e.R e.jr e.area lg w (tWalDir e.area) 0 (W64 1 + k3)
              (tPurgeTok W γ (tPurNames o2) (tPurCand c2) d2.H) (by word)) $$ [H14 H11 H12] as ⟨H14, Htok⟩
          · iframe; iframe #
            unfold tPurgeTok
            iexists d2
            iframe
            ipureintro; exact ⟨hok4, tMemHs_pur hhs2, rfl⟩
          unfold tPurgeTok
          icases Htok with ⟨%d3, H12, H11, %hd3⟩
          obtain ⟨hok5, hhs5, hH5⟩ := hd3
          try wp_auto
          iapply HΦ
          iframe Hlg Hwdir
          simp only [↓reduceIte]
          iexists tPurNames o2
          isplitl
          · iunfold memLive
            iexists w, v1, tPurNames o2, tPurCand c2, d3, t, vo, cm, a, l, tm, M, r, rv3
            iframe
            isplitl [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
            · iunfold memSaveRes
              iframe
              iframe H1 H2 H3 H4 H13 H15
              isplitl []
              · rw [tPurNames_mark, hmk2]; iexact H16
              · rw [hH5, hH2]; iexact H17
            ipureintro
            exact ⟨hok5, hhs5, hfl, tCheckWf_pur hcw2, tMemSim_pur hsim2⟩
          · ipureintro; rw [tPurNames_length, hlen2]; exact Nat.le_refl _
      · try wp_auto
        iapply HΦ
        iframe Hlg Hwdir
        simp only [↓reduceIte]
        iexists tRaiseNames (tSnapO o a ta) a
        isplitl
        · iunfold memLive
          iexists w, v1, tRaiseNames (tSnapO o a ta) a, tRaiseCand (tSnapO o a ta) a c, tReleaseD d1 a, t, vo,
            cm, a, l, tm, M, r, rv2
          iframe
          isplitl [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
          · iunfold memSaveRes
            iframe
            iframe H1 H2 H3 H4 H13 H15
            isplitl []
            · rw [tRaiseNames_mark]; iexact H16
            · rw [tReleaseD_H]; iexact H17
          ipureintro
          exact ⟨hok2, tMemHs_raise hhs1 a, hfl, tCheckWf_raise hcw1 a, tMemSim_raise hsim.2 a⟩
        · ipureintro; rw [tRaiseNames_length, tEncodeOracle_snapO]; exact Nat.le_refl _

end proof

end etcd_wal
end EtcdGrove
end Perennial
