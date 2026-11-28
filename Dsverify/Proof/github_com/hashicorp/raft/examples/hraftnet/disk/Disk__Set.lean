/-
(hraft_robust R3) The proof of `disk.(*Disk).Set`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__Set
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.WriteLemmas
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.copyBytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__persist
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Golang.Theory.IfJoin

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

theorem dk_set_img (I : DiskImg) (stg : w64) (kb vb : List w8) (hok : I.Ok) :
    ({ I with kv := setKV kb vb I.kv } : DiskImg).Pre ∧
    DiskAbs.of { I with kv := setKV kb vb I.kv } stg =
      (DiskOp.stab (.set kb vb)).apply (DiskAbs.of I stg) := by
  refine ⟨⟨hok.idx, setKV_keys kb vb I.kv hok.kvKeys, hok.ikvKeys⟩, ?_⟩
  rw [apply_stab]
  unfold DiskAbs.of DiskImg.absS stabApply
  simp only [setKV_ofList]
  rfl

theorem dk_map_updV_id' {V : Type} (kv : List (List w8 × V)) (kb : List w8) (v : V) (h : kb ∉ kv.map Prod.fst) :
    kv.map (updV kb v) = kv := by
  induction kv with
  | nil => rfl
  | cons p kv ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.map_cons, ih h.2]; unfold updV; rw [if_neg (Ne.symm h.1)]

theorem dk_updV_eq (kb vb : List w8) (p : List w8 × List w8) (h : p.1 = kb) : updV kb vb p = (p.1, vb) := by
  unfold updV; rw [if_pos h]

theorem dk_updV_ne (kb vb : List w8) (p : List w8 × List w8) (h : ¬ p.1 = kb) : updV kb vb p = p := by
  unfold updV; rw [if_neg h]

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.Set.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_bytesEq : github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq.spec (GF := GF) (hG := hG))
    (wp_copyBytes : github_com.hashicorp.raft.examples.hraftnet.disk.copyBytes.spec (GF := GF) (hG := hG))
    (wp_persist : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.persist.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.Set.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf key vsl kb vb
  iintro %Φ #Hdisk #Hkey #Hval Hw HAU
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
  ihave %Hksl := ownSlice_len $$ Hks
  ihave %Hkrl := BigSepL2.bigSepL2_length $$ Hkr
  try wp_auto
  wp_apply (wp_copyBytes vsl DFrac.discard vb) $$ [$Hval] as %c0 ⟨-, Hc0⟩
  ihave >#Hc0 := ownSlice_persist c0 _ _ $$ Hc0
  try wp_auto
  ihave HI : (∃ (i : w64) (fd : Bool) (vss' : List GoSlice), "i" ∷ i_ptr ↦ i ∗ "found" ∷ found_ptr ↦ fd ∗
      "Hks" ∷ ks ↦* kss ∗ "Hvs" ∷ vs ↦* vss' ∗
      "Hvr'" ∷ ([∗list] x; p ∈ vss'; valsAt I.kv kb vb (sint.nat i), x ↦*□ p.2) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ks.len ∧
        (fd = true ↔ kb ∈ (I.kv.take (sint.nat i)).map Prod.fst)⌝ : IProp GF) $$ [i found Hks Hvs]
  · iexists W64 0, false, vss
    rw [show sint.nat (W64 0) = 0 from rfl, valsAt_zero]
    iframe; iframe #; ipureintro
    refine ⟨by word, Hksl.2, by simp⟩
  wp_for HI
  wp_if_destruct
  · have hlt := Hif
    have hil : sint.nat i < kss.length := dk_idx_lt i ks.len _ Hksl Hi.1 hlt
    list_elem kss (sint.nat i) as k
    list_elem I.kv (sint.nat i) as p
    ihave #Hk := BigSepL2.bigSepL2_lookup Hk_lookup Hp_lookup $$ Hkr
    ihave %Hvrl := BigSepL2.bigSepL2_length $$ Hvr'
    ihave %Hvsl := ownSlice_len $$ Hvs
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ks.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index ks (sint.Z i) kss (DFrac.own 1) k Hi.1) $$ [$Hks] as Hks
    · ipureintro; rw [dk_toNat_sint]; exact Hk_lookup
    wp_apply (wp_bytesEq k key DFrac.discard DFrac.discard p.1 kb) $$ [$Hk $Hkey] as ⟨-, -⟩
    obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i ks.len Hi.1 hlt
    wp_if_destruct
    · -- equal: store the value
      have hil2 : sint.nat i < vss'.length := by rw [Hvrl, valsAt_length, ← Hkrl]; exact hil
      list_elem vss' (sint.nat i) as x0
      have hvb : sint.Z i < sint.Z vs.len := by
        have : sint.nat i < sint.nat vs.len := by rw [← Hvsl.1]; exact hil2
        word
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z vs.len from ⟨Hi.1, hvb⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_store_slice_index vs (sint.Z i) _ c0) $$ [$Hvs] as Hvs
      · ipureintro; refine ⟨Hi.1, ?_⟩; have := hil2; word
      try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, true, vss'.set (sint.nat i) c0
      rw [dk_toNat_sint]
      iframe
      rw [hs1, valsAt_step I.kv p.1 vb _ p Hp_lookup, dk_updV_eq p.1 vb p rfl]
      isplitl [Hvr']
      · icases (BigSepL2.bigSepL2_insert_acc Hx0_lookup (valsAt_get I.kv p.1 vb _ p Hp_lookup)) $$ Hvr'
          with ⟨-, Hset⟩
        iapply Hset; iexact Hc0
      ipureintro
      refine ⟨hs2, hs3, ?_⟩
      rw [take_keys_succ I.kv _ p Hp_lookup]; simp
    · try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, fd, vss'
      iframe
      rw [hs1, valsAt_step I.kv kb vb _ p Hp_lookup, dk_updV_ne kb vb p Hif,
        list_set_lookup_self _ _ _ (valsAt_get I.kv kb vb _ p Hp_lookup)]
      iframe
      ipureintro
      refine ⟨hs2, hs3, ?_⟩
      rw [take_keys_succ I.kv _ p Hp_lookup, Hi.2.2]
      simp [Ne.symm Hif]
  · have hie := dk_idx_eq i ks.len _ Hksl Hi.2.1 Hif
    have hlenI : sint.nat i = I.kv.length := by rw [hie, Hkrl]
    rw [hlenI, valsAt_len]
    rw [hlenI, List.take_length] at Hi
    try wp_auto
    rw [show (!fd) = decide (fd = false) by cases fd <;> rfl]
    wp_if_join (fun x => iprop(⌜x = executeVal⌝ ∗ ∃ (ks' vs' : GoSlice) (kss' vss'' : List GoSlice),
        d_ptr ↦ d ∗ key_ptr ↦ key ∗ v_ptr ↦ c0 ∗ d.[Disk, go!"keys"] ↦ ks' ∗ ks' ↦* kss' ∗
        ownSliceCap GoSlice ks' (DFrac.own 1) ∗ ([∗list] k; p ∈ kss'; setKV kb vb I.kv, k ↦*□ p.1) ∗
        d.[Disk, go!"vals"] ↦ vs' ∗ vs' ↦* vss'' ∗ ownSliceCap GoSlice vs' (DFrac.own 1) ∗
        ([∗list] x; p ∈ vss''; setKV kb vb I.kv, x ↦*□ p.2))) with [d key v Hkeys Hks Hkscap Hvals Hvs Hvscap Hvr']
    · -- not found: append the key and the value
      have hnm : kb ∉ I.kv.map Prod.fst := fun h => by have := Hi.2.2.2 h; simp_all
      try wp_auto
      wp_apply (wp_copyBytes key DFrac.discard kb) $$ [$Hkey] as %c ⟨-, Hc⟩
      ihave >#Hc := ownSlice_persist c _ _ $$ Hc
      try wp_auto
      wp_apply (wp_slice_literal (V := GoSlice))
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hlit, -⟩
      wp_apply (wp_slice_append (V := GoSlice)) $$ [$Hks $Hkscap $Hlit] as %ks2 ⟨Hks, Hkscap, -⟩
      try wp_auto
      wp_apply (wp_slice_literal (V := GoSlice))
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hlit2, -⟩
      wp_apply (wp_slice_append (V := GoSlice)) $$ [$Hvs $Hvscap $Hlit2] as %vs2 ⟨Hvs, Hvscap, -⟩
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists ks2, vs2, kss ++ [c], vss' ++ [c0]
      rw [setKV_new kb vb I.kv hnm]
      rw [dk_map_updV_id' I.kv kb vb hnm]
      iframe
      isplitl []
      · iapply BigSepL2.bigSepL2_snoc.2; iframe #
      first
        | (iapply BigSepL2.bigSepL2_singleton.2; iexact Hc0)
        | (iapply BigSepL2.bigSepL2_snoc.2; iframe; iframe #)
    · -- found: the value was replaced in place
      have hm : kb ∈ I.kv.map Prod.fst := Hi.2.2.1 (by cases fd <;> simp_all)
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists ks, vs, kss, vss'
      rw [setKV_found kb vb I.kv hm]
      iframe
      iapply (BigSepL2.bigSepL2_map_right (updV kb vb)).2
      iapply (BigSepL2.bigSepL2_mono (fun {_ _ x2} _ _ => by rw [updV_fst]))
      iexact Hkr
    · iintro %x ⟨%Hx, %ks', %vs', %kss', %vss'', Hd, Hk, Hv, Hkeys, Hks, Hkscap, #Hkr', Hvals, Hvs, Hvscap, #Hvr''⟩
      subst Hx
      obtain ⟨hpre, hab⟩ := dk_set_img I stg kb vb HIok
      ihave Hmem : diskMem d { I with kv := setKV kb vb I.kv } stg $$
          [Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap Hikeys Hiks Hikscap Hivals Hivs Hivscap
           Hstaged Hcommit]
      · iunfold diskMem; iexists es, ks', vs', iks, ivs, lvs, kss', vss'', ikss; iframe; iframe #
      try wp_auto
      wp_bind (App (Val #(methods (go.GoType.PointerType Disk.ty) go!"persist" #d)) (Val #()))
      iapply (wp_persist g d { I with kv := setKV kb vb I.kv } stg qc) $$ Hpkg Hfile [] Hos Hsh Hdinv Hmem Hdh Hcp
      · ipureintro; exact Hf
      iapply (diskWriteAU g Wl Ws Wf I { I with kv := setKV kb vb I.kv } stg (.stab (.set kb vb)) _ hpre hab)
        $$ Hinv Hrec [Hw]
      · simp only [winOf]; iexact Hw
      iintro Hrec Hdh Hcp Hmem
      try wp_auto
      iapply wp_ncfupd _ _ rfl
      iintro Hnc
      imod (diskCommitS g Wl Ws Wf I { I with kv := setKV kb vb I.kv } stg (.set kb vb)
          (fun st => iprop(diskOwnS g { st with bytes := st.bytes.insert kb vb } ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil))
          (Φ #interface.nil)) $$ Hinv Hrec Hlc1 Hlc2 [] HAU Hnc with ⟨Hnc, Hrec, %Hok', HΦ⟩
      · iintro %S HR Hown
        rw [show stabApply (StableOp.set kb vb) S = { S with bytes := S.bytes.insert kb vb } from rfl]
        iapply HR $$ Hown
      imodintro
      iframe Hnc
      try wp_auto
      wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hmem]
      · inext; iunfold diskLockInv; iexists { I with kv := setKV kb vb I.kv }, stg, qc; iframe
        ipureintro; exact Hok'
      try wp_auto
      iexact HΦ

end sec

end Perennial
