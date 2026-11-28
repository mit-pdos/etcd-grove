/-
(hraft_robust R3) The proof of `disk.(*Disk).GetUint64`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__GetUint64
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.InvLemmas
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq
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

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetUint64.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_bytesEq : github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetUint64.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf key kb
  iintro %Φ #Hdisk #Hkey HAU
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
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod (diskReadS g Wl Ws Wf I stg (fun st => Φ (PairV #((st.ints.lookup kb).getD (W64 0)) #interface.nil)))
    $$ Hinv Hrec Hlc1 Hlc2 HAU Hnc with ⟨Hnc, Hrec, HΦ⟩
  imodintro
  iframe Hnc
  rw [show I.absS.ints = GMap.ofList I.ikv from rfl]
  iunfold diskMem at Hmem
  icases Hmem with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  ihave %Hiksl := ownSlice_len $$ Hiks
  ihave %Hikrl := BigSepL2.bigSepL2_length $$ Hikr
  ihave %Hivsl := ownSlice_len $$ Hivs
  try wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Hiks" ∷ iks ↦* ikss ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z iks.len ∧
        ∀ j < sint.nat i, ∀ q, I.ikv[j]? = some q → q.1 ≠ kb⌝ : IProp GF) $$ [i Hiks]
  · iexists W64 0; iframe; ipureintro
    exact ⟨by word, Hiksl.2, fun j hj => by exfalso; rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for HI
  wp_if_destruct
  · have hlt := Hif
    have hil : sint.nat i < ikss.length := dk_idx_lt i iks.len _ Hiksl Hi.1 hlt
    list_elem ikss (sint.nat i) as k
    list_elem I.ikv (sint.nat i) as p
    ihave #Hk := BigSepL2.bigSepL2_lookup Hk_lookup Hp_lookup $$ Hikr
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z iks.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index iks (sint.Z i) ikss (DFrac.own 1) k Hi.1) $$ [$Hiks] as Hiks
    · ipureintro; rw [dk_toNat_sint]; exact Hk_lookup
    wp_apply (wp_bytesEq k key DFrac.discard DFrac.discard p.1 kb) $$ [$Hk $Hkey] as ⟨-, -⟩
    wp_if_destruct
    · -- found
      have hvl : (I.ikv.map Prod.snd)[sint.nat i]? = some p.2 := by
        rw [List.getElem?_map, Hp_lookup]; rfl
      have hvb : sint.Z i < sint.Z ivs.len := by
        have : sint.nat i < sint.nat ivs.len := by
          rw [← Hivsl.1, List.length_map, ← Hikrl]; exact hil
        word
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ivs.len from ⟨Hi.1, hvb⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index ivs (sint.Z i) (I.ikv.map Prod.snd) (DFrac.own 1) p.2 Hi.1) $$ [$Hivs]
        as Hivs
      · ipureintro; rw [dk_toNat_sint]; exact hvl
      try wp_auto
      wp_for_post
      try wp_auto
      wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
        Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
      · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
        isplitl
        · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
        ipureintro; exact HIok
      try wp_auto
      rw [dk_kv_found I.ikv _ p p.1 Hp_lookup rfl Hi.2.2, Option.getD_some]
      iexact HΦ
    · wp_for_post
      iframe
      iexists i + W64 1
      obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i iks.len Hi.1 hlt
      iframe
      ipureintro
      refine ⟨hs2, hs3, ?_⟩
      rw [hs1]
      exact dk_kv_skip I.ikv _ p kb Hp_lookup Hif Hi.2.2
  · have hie := dk_idx_eq i iks.len _ Hiksl Hi.2.1 Hif
    have hnone := ofList_lookup_none' I.ikv kb (dk_kv_none I.ikv kb (by rw [← Hikrl, ← hie]; exact Hi.2.2))
    try wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
      Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
    · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
      isplitl
      · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
      ipureintro; exact HIok
    try wp_auto
    rw [hnone, Option.getD_none]
    iexact HΦ

end sec

end Perennial
