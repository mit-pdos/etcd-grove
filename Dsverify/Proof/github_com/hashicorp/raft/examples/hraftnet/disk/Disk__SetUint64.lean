/-
(hraft_robust R3) The proof of `disk.(*Disk).SetUint64`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__SetUint64
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

theorem dk_setU_img (I : DiskImg) (stg : w64) (kb : List w8) (v : w64) (hok : I.Ok) :
    ({ I with ikv := setKV kb v I.ikv } : DiskImg).Pre ∧
    DiskAbs.of { I with ikv := setKV kb v I.ikv } stg =
      (DiskOp.stab (.setU kb v)).apply (DiskAbs.of I stg) := by
  refine ⟨⟨hok.idx, hok.kvKeys, setKV_keys kb v I.ikv hok.ikvKeys⟩, ?_⟩
  rw [apply_stab]
  unfold DiskAbs.of DiskImg.absS stabApply
  simp only [setKV_ofList]
  rfl

theorem dk_vals_set (kv : List (List w8 × w64)) (kb : List w8) (v : w64) (i : Nat) (p : List w8 × w64)
    (hp : kv[i]? = some p) (h : p.1 = kb) :
    ((valsAt kv kb v i).map Prod.snd).set i v = (valsAt kv kb v (i + 1)).map Prod.snd := by
  rw [valsAt_step kv kb v i p hp, List.map_set]
  unfold updV; rw [if_pos h]

theorem dk_vals_same (kv : List (List w8 × w64)) (kb : List w8) (v : w64) (i : Nat) (p : List w8 × w64)
    (hp : kv[i]? = some p) (h : ¬ p.1 = kb) :
    (valsAt kv kb v i).map Prod.snd = (valsAt kv kb v (i + 1)).map Prod.snd := by
  rw [valsAt_step kv kb v i p hp]
  unfold updV; rw [if_neg h, list_set_lookup_self _ _ _ (valsAt_get kv kb v i p hp)]

theorem dk_map_updV_id {V : Type} (kv : List (List w8 × V)) (kb : List w8) (v : V) (h : kb ∉ kv.map Prod.fst) :
    kv.map (updV kb v) = kv := by
  induction kv with
  | nil => rfl
  | cons p kv ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.map_cons, ih h.2]; unfold updV; rw [if_neg (Ne.symm h.1)]

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.SetUint64.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_bytesEq : github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq.spec (GF := GF) (hG := hG))
    (wp_copyBytes : github_com.hashicorp.raft.examples.hraftnet.disk.copyBytes.spec (GF := GF) (hG := hG))
    (wp_persist : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.persist.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.SetUint64.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf key kb v
  iintro %Φ #Hdisk #Hkey Hw HAU
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
  ihave %Hiksl := ownSlice_len $$ Hiks
  ihave %Hikrl := BigSepL2.bigSepL2_length $$ Hikr
  ihave %Hivsl := ownSlice_len $$ Hivs
  try wp_auto
  ihave HI : (∃ (i : w64) (fd : Bool), "i" ∷ i_ptr ↦ i ∗ "found" ∷ found_ptr ↦ fd ∗ "Hiks" ∷ iks ↦* ikss ∗
      "Hivs" ∷ ivs ↦* (valsAt I.ikv kb v (sint.nat i)).map Prod.snd ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z iks.len ∧
        (fd = true ↔ kb ∈ (I.ikv.take (sint.nat i)).map Prod.fst)⌝ : IProp GF) $$ [i found Hiks Hivs]
  · iexists W64 0, false
    rw [show sint.nat (W64 0) = 0 from rfl, valsAt_zero]
    iframe; ipureintro
    refine ⟨by word, Hiksl.2, by simp⟩
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
    obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i iks.len Hi.1 hlt
    wp_if_destruct
    · -- equal: store the value
      have hvb : sint.Z i < sint.Z ivs.len := by
        have : sint.nat i < sint.nat ivs.len := by
          rw [← Hivsl.1, List.length_map, ← Hikrl]; exact hil
        word
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ivs.len from ⟨Hi.1, hvb⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_store_slice_index ivs (sint.Z i) _ v) $$ [$Hivs] as Hivs
      · ipureintro
        refine ⟨Hi.1, ?_⟩
        simp only [List.length_map, valsAt_length]
        have := Hikrl; have := hil; word
      try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, true
      iframe
      rw [hs1, ← dk_vals_set I.ikv p.1 v _ p Hp_lookup rfl, dk_toNat_sint]
      iframe
      ipureintro
      refine ⟨hs2, hs3, ?_⟩
      rw [take_keys_succ I.ikv _ p Hp_lookup]; simp
    · try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, fd
      iframe
      rw [hs1, ← dk_vals_same I.ikv kb v _ p Hp_lookup Hif]
      iframe
      ipureintro
      refine ⟨hs2, hs3, ?_⟩
      rw [take_keys_succ I.ikv _ p Hp_lookup, Hi.2.2]
      simp [Ne.symm Hif]
  · have hie := dk_idx_eq i iks.len _ Hiksl Hi.2.1 Hif
    have hlenI : sint.nat i = I.ikv.length := by rw [hie, Hikrl]
    rw [hlenI, valsAt_len]
    rw [hlenI, List.take_length] at Hi
    try wp_auto
    rw [show (!fd) = decide (fd = false) by cases fd <;> rfl]
    wp_if_join (fun x => iprop(⌜x = executeVal⌝ ∗ ∃ (iks' ivs' : GoSlice) (ikss' : List GoSlice),
        d_ptr ↦ d ∗ key_ptr ↦ key ∗ val_ptr ↦ v ∗ d.[Disk, go!"ikeys"] ↦ iks' ∗ iks' ↦* ikss' ∗ ownSliceCap GoSlice iks' (DFrac.own 1) ∗
        ([∗list] k; p ∈ ikss'; setKV kb v I.ikv, k ↦*□ p.1) ∗
        d.[Disk, go!"ivals"] ↦ ivs' ∗ ivs' ↦* ((setKV kb v I.ikv).map Prod.snd) ∗
        ownSliceCap w64 ivs' (DFrac.own 1))) with [d key val Hikeys Hiks Hikscap Hivals Hivs Hivscap]
    · -- not found: append the key and the value
      have hnm : kb ∉ I.ikv.map Prod.fst := fun h => by have := Hi.2.2.2 h; simp_all
      try wp_auto
      wp_apply (wp_copyBytes key DFrac.discard kb) $$ [$Hkey] as %c ⟨-, Hc⟩
      ihave >#Hc := ownSlice_persist c _ _ $$ Hc
      try wp_auto
      wp_apply (wp_slice_literal (V := GoSlice))
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hlit, -⟩
      wp_apply (wp_slice_append (V := GoSlice)) $$ [$Hiks $Hikscap $Hlit] as %iks2 ⟨Hiks, Hikscap, -⟩
      try wp_auto
      wp_apply (wp_slice_literal (V := w64))
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hlit2, -⟩
      wp_apply (wp_slice_append (V := w64)) $$ [$Hivs $Hivscap $Hlit2] as %ivs2 ⟨Hivs, Hivscap, -⟩
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists iks2, ivs2, ikss ++ [c]
      rw [setKV_new kb v I.ikv hnm]
      rw [dk_map_updV_id I.ikv kb v hnm]
      simp only [List.map_append, List.map_cons, List.map_nil]
      iframe
      iapply BigSepL2.bigSepL2_snoc.2
      iframe #
    · -- found: the value was replaced in place
      have hm : kb ∈ I.ikv.map Prod.fst := Hi.2.2.1 (by cases fd <;> simp_all)
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists iks, ivs, ikss
      rw [setKV_found kb v I.ikv hm]
      iframe
      iapply (BigSepL2.bigSepL2_map_right (updV kb v)).2
      iapply (BigSepL2.bigSepL2_mono (fun {_ _ x2} _ _ => by rw [updV_fst]))
      iexact Hikr
    · iintro %x ⟨%Hx, %iks', %ivs', %ikss', Hd, Hk, Hv, Hikeys, Hiks, Hikscap, #Hikr', Hivals, Hivs, Hivscap⟩
      subst Hx
      obtain ⟨hpre, hab⟩ := dk_setU_img I stg kb v HIok
      ihave Hmem : diskMem d { I with ikv := setKV kb v I.ikv } stg $$
          [Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap Hikeys Hiks Hikscap Hivals Hivs Hivscap
           Hstaged Hcommit]
      · iunfold diskMem; iexists es, ks, vs, iks', ivs', lvs, kss, vss, ikss'; iframe; iframe #
      try wp_auto
      wp_bind (App (Val #(methods (go.GoType.PointerType Disk.ty) go!"persist" #d)) (Val #()))
      iapply (wp_persist g d { I with ikv := setKV kb v I.ikv } stg qc) $$ Hpkg Hfile [] Hos Hsh Hdinv Hmem Hdh Hcp
      · ipureintro; exact Hf
      iapply (diskWriteAU g Wl Ws Wf I { I with ikv := setKV kb v I.ikv } stg (.stab (.setU kb v)) _ hpre hab)
        $$ Hinv Hrec [Hw]
      · simp only [winOf]; iexact Hw
      iintro Hrec Hdh Hcp Hmem
      try wp_auto
      iapply wp_ncfupd _ _ rfl
      iintro Hnc
      imod (diskCommitS g Wl Ws Wf I { I with ikv := setKV kb v I.ikv } stg (.setU kb v)
          (fun st => iprop(diskOwnS g { st with ints := st.ints.insert kb v } ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil))
          (Φ #interface.nil)) $$ Hinv Hrec Hlc1 Hlc2 [] HAU Hnc with ⟨Hnc, Hrec, %Hok', HΦ⟩
      · iintro %S HR Hown
        rw [show stabApply (StableOp.setU kb v) S = { S with ints := S.ints.insert kb v } from rfl]
        iapply HR $$ Hown
      imodintro
      iframe Hnc
      try wp_auto
      wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hmem]
      · inext; iunfold diskLockInv; iexists { I with ikv := setKV kb v I.ikv }, stg, qc; iframe
        ipureintro; exact Hok'
      try wp_auto
      iexact HΦ
