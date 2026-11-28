/-
(hraft_robust R3) The proof of `disk.(*Disk).FirstIndex`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__FirstIndex
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.InvLemmas
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

/-- What `FirstIndex` returns for the image `I`. -/
def dkFirst (I : DiskImg) : w64 := match I.ents with
  | [] => W64 0
  | e :: _ => e.idx

theorem dk_first_ok (I : DiskImg) (stg : w64) (hok : I.Ok) :
    (uint.nat (dkFirst I) = 0 ∧ (I.absL stg).m = ∅) ∨
      (((I.absL stg).m.lookup (uint.nat (dkFirst I))).isSome ∧
        ∀ k e, (I.absL stg).m.lookup k = some e → uint.nat (dkFirst I) ≤ k) := by
  unfold dkFirst
  cases h : I.ents with
  | nil => left; exact ⟨rfl, logM_empty I h⟩
  | cons e es => right; exact first_min I e es h hok.idx

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.FirstIndex.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.FirstIndex.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf
  iintro %Φ #Hdisk HAU
  iunfold isDisk at Hdisk
  icases Hdisk with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply (lc := 2) wp_Lock $$ [$Hisl] as ⟨Hlocked, HR⟩
  iunfold diskLockInv at HR
  icases HR with ⟨%I, %stg, %qc, Hmem, Hrec, %HIok, Hdh, Hcp⟩
  ihave Hc : iprop(|NC={⊤}=> ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.idle) : DiskRec) ∗
      Φ (PairV #(dkFirst I) #interface.nil)) $$ [HAU Hrec Hlc1 Hlc2]
  · icases HAU with (HAU | HAU)
    · iintro Hnc
      imod (diskReadL g Wl Ws Wf I stg (fun A => iprop(∀ r : w64,
          ⌜(uint.nat r = 0 ∧ A.m = ∅) ∨
            ((A.m.lookup (uint.nat r)).isSome ∧ ∀ k e, A.m.lookup k = some e → uint.nat r ≤ k)⌝ -∗
          Φ (PairV #r #interface.nil)))) $$ Hinv Hrec Hlc1 Hlc2 HAU Hnc with ⟨Hnc, Hrec, HΦ⟩
      imodintro; iframe Hnc Hrec; iapply HΦ; ipureintro; exact dk_first_ok I stg HIok
    · iintro Hnc; imodintro; iframe; iapply HAU
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod Hc $$ Hnc with ⟨Hnc, Hrec, HΦ⟩
  imodintro
  iframe Hnc
  iunfold diskMem at Hmem
  icases Hmem with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hentl := BigSepL2.bigSepL2_length $$ Hent
  try wp_auto
  wp_if_destruct
  · have hnil : I.ents = [] := by
      rw [← List.length_eq_zero_iff, ← Hentl, Hesl.1, Hif]; rfl
    try wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
      Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
    · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
      isplitl
      · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
      ipureintro; exact HIok
    try wp_auto
    rw [show dkFirst I = W64 0 by unfold dkFirst; rw [hnil]]
    iexact HΦ
  · have hpos : 0 < lvs.length := by
      have : sint.nat es.len ≠ 0 := by intro h; apply Hif; word
      omega
    list_elem lvs 0 as lv
    list_elem I.ents 0 as e
    ihave #Her := BigSepL2.bigSepL2_lookup Hlv_lookup He_lookup $$ Hent
    iunfold entRep at Her
    icases Her with ⟨%Hef, -, -⟩
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len := by
      have : sint.nat es.len ≠ 0 := by intro h; apply Hif; word
      constructor <;> word
    icases ownSlice_elem_acc (sint.Z (W64 0)) lv es (DFrac.own 1) lvs hb.1 Hlv_lookup $$ Hes with ⟨Hv, Hclose⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    try wp_auto
    ihave Hes := Hclose $$ Hv
    rw [list_set_lookup_self lvs (sint.Z (W64 0)).toNat lv (by exact Hlv_lookup)]
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
      Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
    · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
      isplitl
      · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
      ipureintro; exact HIok
    try wp_auto
    have hfe : dkFirst I = lv.Index' := by
      have he : I.ents = e :: I.ents.tail := by
        cases h : I.ents with
        | nil => rw [h] at He_lookup; simp at He_lookup
        | cons f fs => rw [h] at He_lookup; simp at He_lookup; rw [He_lookup]; rfl
      unfold dkFirst; rw [he]; exact Hef.1.symm
    rw [hfe]
    iexact HΦ

end sec

end Perennial
