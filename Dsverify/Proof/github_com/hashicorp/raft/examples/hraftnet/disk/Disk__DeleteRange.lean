/-
(hraft_robust R3) The proof of `disk.(*Disk).DeleteRange`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__DeleteRange
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.WriteLemmas
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__persist
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

theorem dk_del_keep (mn mx : w64) (ents : List DEnt) (i : Nat) (e : DEnt) (he : ents[i]? = some e)
    (hk : uint.Z e.idx < uint.Z mn ∨ uint.Z mx < uint.Z e.idx) :
    delEnts mn mx (ents.take (i + 1)) = delEnts mn mx (ents.take i) ++ [e] := by
  unfold delEnts
  rw [List.take_add_one, he]
  simp only [Option.toList_some, List.filter_append, List.filter_cons, List.filter_nil]
  have : decide (¬(uint.nat mn ≤ uint.nat e.idx ∧ uint.nat e.idx ≤ uint.nat mx)) = true := by
    simp only [decide_eq_true_eq]; intro h; rcases hk with hk | hk <;> word
  rw [if_pos this]

theorem dk_del_drop (mn mx : w64) (ents : List DEnt) (i : Nat) (e : DEnt) (he : ents[i]? = some e)
    (hk1 : ¬ uint.Z e.idx < uint.Z mn) (hk2 : ¬ uint.Z mx < uint.Z e.idx) :
    delEnts mn mx (ents.take (i + 1)) = delEnts mn mx (ents.take i) := by
  unfold delEnts
  rw [List.take_add_one, he]
  simp only [Option.toList_some, List.filter_append, List.filter_cons, List.filter_nil]
  have : decide (¬(uint.nat mn ≤ uint.nat e.idx ∧ uint.nat e.idx ≤ uint.nat mx)) = false := by
    simp only [decide_eq_false_iff_not, Classical.not_not]; constructor <;> word
  rw [if_neg (by rw [this]; simp), List.append_nil]

theorem dk_del_img (I : DiskImg) (stg : w64) (main : Bool) (mn mx : w64) (hok : I.Ok) :
    (delImg I mn mx).Pre ∧
    DiskAbs.of (delImg I mn mx) stg = (DiskOp.log (.del main (uint.nat mn) (uint.nat mx))).apply (DiskAbs.of I stg) := by
  obtain ⟨h1, h2⟩ := delImg_absL I stg mn mx hok.idx
  refine ⟨⟨h2, hok.kvKeys, hok.ikvKeys⟩, ?_⟩
  rw [apply_log]
  unfold DiskAbs.of
  simp only [logApply]
  rw [h1]; rfl

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.DeleteRange.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_persist : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.persist.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf main mn mx
  iintro %Φ #Hdisk Hw HAU
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
  iunfold diskMem at Hmem
  icases Hmem with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hentl := BigSepL2.bigSepL2_length $$ Hent
  try wp_auto
  ihave HI : (∃ (i : w64) (nsl : GoSlice) (nlvs : List Log), "i" ∷ i_ptr ↦ i ∗ "ents" ∷ ents_ptr ↦ nsl ∗
      "Hn" ∷ nsl ↦* nlvs ∗ "Hncap" ∷ ownSliceCap Log nsl (DFrac.own 1) ∗ "Hes" ∷ es ↦* lvs ∗
      "#Hnr" ∷ ([∗list] lv; e ∈ nlvs; delEnts mn mx (I.ents.take (sint.nat i)), entRep lv e) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z es.len⌝ : IProp GF) $$ [i ents Hes]
  · iexists W64 0, slice.nil, []
    rw [show sint.nat (W64 0) = 0 from rfl]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · rw [List.take_zero]; simp only [delEnts, List.filter_nil]
      iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; exact ⟨by word, Hesl.2⟩
  wp_for HI
  wp_if_destruct
  · have hlt := Hif
    have hil : sint.nat i < lvs.length := dk_idx_lt i es.len _ Hesl Hi.1 hlt
    list_elem lvs (sint.nat i) as lv
    list_elem I.ents (sint.nat i) as e
    ihave #Her := BigSepL2.bigSepL2_lookup Hlv_lookup He_lookup $$ Hent
    ihave #Her' := Her
    iunfold entRep at Her'
    icases Her' with ⟨%Hef, -, -⟩
    obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i es.len Hi.1 hlt
    icases ownSlice_elem_acc (sint.Z i) lv es (DFrac.own 1) lvs Hi.1
      (by rw [dk_toNat_sint]; exact Hlv_lookup) $$ Hes with ⟨Hv, Hclose⟩
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · -- below mn: kept
      ihave Hes := Hclose $$ Hv
      rw [list_set_lookup_self lvs _ lv (by rw [dk_toNat_sint]; exact Hlv_lookup)]
      try wp_auto
      try simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index es (sint.Z i) lvs (DFrac.own 1) lv Hi.1) $$ [$Hes] as Hes
      · ipureintro; rw [dk_toNat_sint]; exact Hlv_lookup
      try wp_auto
      wp_apply (wp_slice_literal (V := Log))
      isplitr
      · ipureintro; rfl
      iintro %slp ⟨Hlit, -⟩
      wp_apply (wp_slice_append (V := Log)) $$ [$Hn $Hncap $Hlit] as %n2 ⟨Hn, Hncap, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, n2, nlvs ++ [lv]
      iframe
      rw [hs1, dk_del_keep mn mx I.ents _ e He_lookup (Or.inl (by rw [← Hef.1]; exact Hif))]
      isplitl
      · iapply BigSepL2.bigSepL2_snoc.2; iframe #
      ipureintro; exact ⟨hs2, hs3⟩
    · have hlo := Hif
      try wp_auto
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
      try wp_auto
      wp_if_destruct
      · -- above mx: kept
        ihave Hes := Hclose $$ Hv
        rw [list_set_lookup_self lvs _ lv (by rw [dk_toNat_sint]; exact Hlv_lookup)]
        try wp_auto
        try simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index es (sint.Z i) lvs (DFrac.own 1) lv Hi.1) $$ [$Hes] as Hes
        · ipureintro; rw [dk_toNat_sint]; exact Hlv_lookup
        try wp_auto
        wp_apply (wp_slice_literal (V := Log))
        isplitr
        · ipureintro; rfl
        iintro %slp ⟨Hlit, -⟩
        wp_apply (wp_slice_append (V := Log)) $$ [$Hn $Hncap $Hlit] as %n2 ⟨Hn, Hncap, -⟩
        try wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, n2, nlvs ++ [lv]
        iframe
        rw [hs1, dk_del_keep mn mx I.ents _ e He_lookup (Or.inr (by rw [← Hef.1]; exact Hif))]
        isplitl
        · iapply BigSepL2.bigSepL2_snoc.2; iframe #
        ipureintro; exact ⟨hs2, hs3⟩
      · -- in the range: dropped
        ihave Hes := Hclose $$ Hv
        rw [list_set_lookup_self lvs _ lv (by rw [dk_toNat_sint]; exact Hlv_lookup)]
        try wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, nsl, nlvs
        iframe
        rw [hs1, dk_del_drop mn mx I.ents _ e He_lookup (by rw [← Hef.1]; exact hlo) (by rw [← Hef.1]; exact Hif)]
        iframe #
        ipureintro; exact ⟨hs2, hs3⟩
  · have hie := dk_idx_eq i es.len _ Hesl Hi.2 Hif
    rw [hie, Hentl, List.take_length]
    try wp_auto
    obtain ⟨hpre, hab⟩ := dk_del_img I stg main mn mx HIok
    ihave Hmem : diskMem d (delImg I mn mx) stg $$
        [Hents Hn Hncap Hkeys Hks Hkscap Hvals Hvs Hvscap Hikeys Hiks Hikscap Hivals Hivs Hivscap
         Hstaged Hcommit]
    · iunfold diskMem; simp only [delImg]
      iexists nsl, ks, vs, iks, ivs, nlvs, kss, vss, ikss; iframe; iframe #
    wp_bind (App (Val #(methods (go.GoType.PointerType Disk.ty) go!"persist" #d)) (Val #()))
    iapply (wp_persist g d (delImg I mn mx) stg qc) $$ Hpkg Hfile [] Hos Hsh Hdinv Hmem Hdh Hcp
    · ipureintro; exact Hf
    iapply (diskWriteAU g Wl Ws Wf I (delImg I mn mx) stg (.log (.del main (uint.nat mn) (uint.nat mx))) _ hpre hab)
      $$ Hinv Hrec [Hw]
    · simp only [winOf]; iexact Hw
    iintro Hrec Hdh Hcp Hmem
    try wp_auto
    iapply wp_ncfupd _ _ rfl
    iintro Hnc
    imod (diskCommitL g Wl Ws Wf I (delImg I mn mx) stg (.del main (uint.nat mn) (uint.nat mx))
        (fun A => iprop(∀ hi' : w64, diskOwnL g (A.delete (uint.nat mn) (uint.nat mx) hi') ={∅,⊤ \ ↑storeN}=∗
          Φ #interface.nil))
        (Φ #interface.nil)) $$ Hinv Hrec Hlc1 Hlc2 [] HAU Hnc with ⟨Hnc, Hrec, %Hok', HΦ⟩
    · iintro %A HR Hown
      rw [show logApply (LogOp.del main (uint.nat mn) (uint.nat mx)) A =
        A.delete (uint.nat mn) (uint.nat mx) (maxKey (LogAbs.del A.m (uint.nat mn) (uint.nat mx))) from rfl]
      iapply HR $$ Hown
    imodintro
    iframe Hnc
    try wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hmem]
    · inext; iunfold diskLockInv; iexists delImg I mn mx, stg, qc; iframe
      ipureintro; exact Hok'
    try wp_auto
    iexact HΦ

end sec

end Perennial
