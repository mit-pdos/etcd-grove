/-
(hraft_robust R3) The proof of `disk.(*Disk).Get`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__Get
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.InvLemmas
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.copyBytes
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

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.Get.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_bytesEq : github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq.spec (GF := GF) (hG := hG))
    (wp_copyBytes : github_com.hashicorp.raft.examples.hraftnet.disk.copyBytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.Get.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf key kb
  iintro %Φ #Hdisk #Hkey HAU
  iunfold isDisk at Hdisk
  icases Hdisk with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
  ihave #Hinit := isInit_access $$ Hpkg
  iNamed Hinit
  iunfold errors.newVar at HErrNotFound
  icases HErrNotFound with ⟨%xnf, #Hgnf, #Hsnf, -⟩
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply (lc := 2) wp_Lock $$ [$Hisl] as ⟨Hlocked, HR⟩
  iunfold diskLockInv at HR
  icases HR with ⟨%I, %stg, %qc, Hmem, Hrec, %HIok, Hdh, Hcp⟩
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod (diskReadS g Wl Ws Wf I stg (fun st => iprop(
      (∀ vb, ⌜st.bytes.lookup kb = some vb⌝ -∗ ∀ s : GoSlice, s ↦*□ vb -∗ Φ (PairV #s #interface.nil)) ∧
      (⌜∀ vb, st.bytes.lookup kb = some vb → vb = []⌝ -∗
        ∀ err : GoInterface, isNotFoundErr err -∗ Φ (PairV #(Perennial.zero_val GoSlice) #err)))))
    $$ Hinv Hrec Hlc1 Hlc2 HAU Hnc with ⟨Hnc, Hrec, HΦ⟩
  imodintro
  iframe Hnc
  rw [show I.absS.bytes = GMap.ofList I.kv from rfl]
  iunfold diskMem at Hmem
  icases Hmem with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  ihave %Hksl := ownSlice_len $$ Hks
  ihave %Hkrl := BigSepL2.bigSepL2_length $$ Hkr
  ihave %Hvsl := ownSlice_len $$ Hvs
  ihave %Hvrl := BigSepL2.bigSepL2_length $$ Hvr
  try wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Hks" ∷ ks ↦* kss ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ks.len ∧
        ∀ j < sint.nat i, ∀ q, I.kv[j]? = some q → q.1 ≠ kb⌝ : IProp GF) $$ [i Hks]
  · iexists W64 0; iframe; ipureintro
    exact ⟨by word, Hksl.2, fun j hj => by exfalso; rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for HI
  wp_if_destruct
  · have hlt := Hif
    have hil : sint.nat i < kss.length := dk_idx_lt i ks.len _ Hksl Hi.1 hlt
    list_elem kss (sint.nat i) as k
    list_elem vss (sint.nat i) as v
    list_elem I.kv (sint.nat i) as p
    ihave #Hk := BigSepL2.bigSepL2_lookup Hk_lookup Hp_lookup $$ Hkr
    ihave #Hv := BigSepL2.bigSepL2_lookup Hv_lookup Hp_lookup $$ Hvr
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ks.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index ks (sint.Z i) kss (DFrac.own 1) k Hi.1) $$ [$Hks] as Hks
    · ipureintro; rw [dk_toNat_sint]; exact Hk_lookup
    wp_apply (wp_bytesEq k key DFrac.discard DFrac.discard p.1 kb) $$ [$Hk $Hkey] as ⟨-, -⟩
    wp_if_destruct
    · -- found
      have hvb : sint.Z i < sint.Z vs.len := by
        have : sint.nat i < sint.nat vs.len := by rw [← Hvsl.1, Hvrl, ← Hkrl]; exact hil
        word
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z vs.len from ⟨Hi.1, hvb⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index vs (sint.Z i) vss (DFrac.own 1) v Hi.1) $$ [$Hvs] as Hvs
      · ipureintro; rw [dk_toNat_sint]; exact Hv_lookup
      wp_apply wp_copyBytes $$ [$Hv] as %c ⟨-, Hc⟩
      try wp_auto
      wp_for_post
      try wp_auto
      ihave >#Hc := ownSlice_persist c _ _ $$ Hc
      wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
        Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
      · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
        isplitl
        · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
        ipureintro; exact HIok
      try wp_auto
      icases HΦ with ⟨HΦ, -⟩
      iapply HΦ $$ %p.2 %(dk_kv_found I.kv _ p p.1 Hp_lookup rfl Hi.2.2) %c Hc
    · wp_for_post
      iframe
      iexists i + W64 1
      obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i ks.len Hi.1 hlt
      iframe
      ipureintro
      refine ⟨hs2, hs3, ?_⟩
      rw [hs1]
      exact dk_kv_skip I.kv _ p kb Hp_lookup Hif Hi.2.2
  · have hie := dk_idx_eq i ks.len _ Hksl Hi.2.1 Hif
    have hnone := ofList_lookup_none' I.kv kb (dk_kv_none I.kv kb (by rw [← Hkrl, ← hie]; exact Hi.2.2))
    try wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
      Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
    · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
      isplitl
      · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
      ipureintro; exact HIok
    try wp_auto
    icases HΦ with ⟨-, HΦ⟩
    iapply HΦ
    · ipureintro; intro vb h; rw [hnone] at h; cases h
    · iunfold isNotFoundErr; iexists xnf; iframe #; ipureintro; rfl

end sec

end Perennial
