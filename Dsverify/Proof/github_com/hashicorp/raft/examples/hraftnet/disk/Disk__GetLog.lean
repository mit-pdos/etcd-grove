/-
(hraft_robust R3) The proof of `disk.(*Disk).GetLog`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__GetLog
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

theorem dk_getlog_skip (ents : List DEnt) (i : Nat) (e : DEnt) (idx : w64) (he : ents[i]? = some e)
    (hne : e.idx ≠ idx) (h : ∀ j < i, ∀ f, ents[j]? = some f → f.idx ≠ idx) :
    ∀ j < i + 1, ∀ f, ents[j]? = some f → f.idx ≠ idx := by
  intro j hj f hf
  by_cases hji : j = i
  · subst hji; rw [he] at hf; cases hf; exact hne
  · exact h j (by omega) f hf

theorem dk_getlog_none (ents : List DEnt) (idx : w64)
    (h : ∀ j < ents.length, ∀ f, ents[j]? = some f → f.idx ≠ idx) : ∀ e ∈ ents, e.idx ≠ idx := by
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  exact h j hj _ (List.getElem?_eq_getElem hj)

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetLog.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetLog.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf idx ptr lv0
  iintro %Φ #Hdisk Hptr HAU
  iunfold isDisk at Hdisk
  icases Hdisk with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft $$ []
  · iPkgInit
  icases dk_isRaftErr_of_init .logNotFound $$ Hraft with ⟨%e0, #He0⟩
  ihave #Hg0 : (globalAddr ErrLogNotFound ↦□ e0 : IProp GF) $$ []
  · have h := dk_isRaftErr_global (GF := GF) .logNotFound e0
    rw [show RaftErr.logNotFound.var = ErrLogNotFound from rfl] at h
    iapply h $$ He0
  ihave %Hne0 := dk_isRaftErr_nonnil .logNotFound e0 $$ He0
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
  imod (diskReadL g Wl Ws Wf I stg
      (fun A => iprop(∀ err : GoInterface, getLogPost ptr (uint.nat idx) A.m err -∗ Φ #err)))
    $$ Hinv Hrec Hlc1 Hlc2 HAU Hnc with ⟨Hnc, Hrec, HΦ⟩
  imodintro
  iframe Hnc
  iunfold diskMem at Hmem
  icases Hmem with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hentl := BigSepL2.bigSepL2_length $$ Hent
  try wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Hes" ∷ es ↦* lvs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z es.len ∧
        ∀ j < sint.nat i, ∀ f, I.ents[j]? = some f → f.idx ≠ idx⌝ : IProp GF) $$ [i Hes]
  · iexists W64 0; iframe; ipureintro; refine ⟨by word, Hesl.2, fun j hj => by exfalso; rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for HI
  wp_if_destruct
  · have hlt := Hif
    have hil : sint.nat i < lvs.length := dk_idx_lt i es.len _ Hesl Hi.1 hlt
    list_elem lvs (sint.nat i) as lv
    list_elem I.ents (sint.nat i) as e
    ihave #Her := BigSepL2.bigSepL2_lookup Hlv_lookup He_lookup $$ Hent
    iunfold entRep at Her
    icases Her with ⟨%Hef, #Hdata, #Hext⟩
    icases ownSlice_elem_acc (sint.Z i) lv es (DFrac.own 1) lvs Hi.1
      (by rw [dk_toNat_sint]; exact Hlv_lookup) $$ Hes with ⟨Hv, Hclose⟩
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · -- found
      ihave Hes := Hclose $$ Hv
      rw [list_set_lookup_self lvs _ lv (by rw [dk_toNat_sint]; exact Hlv_lookup)]
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index es (sint.Z i) lvs (DFrac.own 1) lv Hi.1) $$ [$Hes] as Hes
      · ipureintro; rw [dk_toNat_sint]; exact Hlv_lookup
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
      iapply HΦ
      unfold getLogPost
      have hk : uint.nat lv.Index' = uint.nat e.idx := by rw [Hef.1]
      rw [show (I.absL stg).m = I.logM from rfl, hk, logM_lookup_at I _ e He_lookup HIok.idx]
      isplitr
      · ipureintro; rfl
      iexists lv; iframe
      unfold logIs
      iframe #
      isplitr
      · ipureintro
        refine ⟨by rw [Hef.1], by rw [Hef.2.1]; rfl, by rw [Hef.2.2]; rfl⟩
      rw [show (entOf e).data = e.data from rfl]
      iexact Hdata
    · ihave Hes := Hclose $$ Hv
      rw [list_set_lookup_self lvs _ lv (by rw [dk_toNat_sint]; exact Hlv_lookup)]
      wp_for_post
      iframe
      iexists i + W64 1
      obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i es.len Hi.1 hlt
      iframe
      ipureintro
      refine ⟨hs2, hs3, ?_⟩
      rw [hs1]
      exact dk_getlog_skip I.ents _ e idx He_lookup (by rw [← Hef.1]; exact Hif) Hi.2.2
  · -- not found
    have hie := dk_idx_eq i es.len _ Hesl Hi.2.1 Hif
    have hnone := logM_lookup_none I idx (dk_getlog_none I.ents idx (by rw [← Hentl, ← hie]; exact Hi.2.2))
    try wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
      Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
    · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
      isplitl
      · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
      ipureintro; exact HIok
    try wp_auto
    iapply HΦ
    unfold getLogPost
    rw [show (I.absL stg).m = I.logM from rfl, hnone]
    isplitr
    · ipureintro; exact Hne0
    isplitr
    · iexists .logNotFound; iexact He0
    · iexists lv0; iframe

end sec

end Perennial
