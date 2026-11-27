/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/checkConfiguration.lean (241f27e).
-/
/-
The proof of `raft.checkConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.checkConfiguration
public import Dsverify.Proof.github_com.hashicorp.raft.EncodingLemmas
public import Dsverify.Proof.github_com.hashicorp.raft.FmtErrorf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

/-- (helper) The voters of the first `k+1` servers. -/
theorem checkConfiguration.srvVoters_take_succ (ss : List Server) (k : Nat) (sk : Server)
    (h : ss[k]? = some sk) :
    (srvVoters (ss.take (k + 1))).length =
      (srvVoters (ss.take k)).length + (if sk.Suffrage' = W64 0 then 1 else 0) := by
  unfold srvVoters
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.filter_append, List.map_append, List.length_append,
    List.filter_cons, List.filter_nil, List.length_map]
  split <;> simp_all

/-- (helper) At most `k` voters among the first `k` servers. -/
theorem checkConfiguration.srvVoters_take_le (ss : List Server) (k : Nat) :
    (srvVoters (ss.take k)).length ≤ k := by
  unfold srvVoters
  rw [List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp [Nat.min_le_left])

/-- `fmt.wp_Errorf_cfgErr` is a premise (port, 2026-11-27): Perennial's `fmt` model is stuck on `%v` of
a struct, so `fmt.Errorf.spec_cfgErr` has no proof (`FmtErrorf.lean`); the link discharges it. -/
theorem github_com.hashicorp.raft.checkConfiguration.wp_proof
    (wp_Errorf_cfgErr : fmt.Errorf.spec_cfgErr (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.checkConfiguration.spec (GF := GF) (hG := hG) := by
  intro c ss dq
  wp_start as ⟨Hs, %Hok⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %mid Hmid
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %mad Hmad
  obtain ⟨Hsrv, Hnd⟩ := Hok
  ihave HI : (∃ (k : w64) (sv0 : Server) (v : w64),
      "i" ∷ i_ptr ↦ k ∗ "server" ∷ server_ptr ↦ sv0 ∗ "voters" ∷ voters_ptr ↦ v ∗
      "Hmid" ∷ mid ↦$ keySet (fun s => s.ID') (ss.take (sint.nat k)) ∗
      "Hmad" ∷ mad ↦$ keySet (fun s => s.Address') (ss.take (sint.nat k)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z c.Servers'.len ∧
        v = W64 (srvVoters (ss.take (sint.nat k))).length⌝ : IProp GF)
      $$ [i server voters Hmid Hmad]
  · iexists W64 0, _, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · rw [if_pos (by word)]
    list_elem ss (sint.nat k) as sv
    wp_apply (wp_load_slice_index c.Servers' (sint.Z k) ss dq sv Hk.1) $$ [$Hs] as Hs
    · ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact Hsv_lookup
    obtain ⟨hadr, hid⟩ := Hsrv sv (List.mem_of_getElem? Hsv_lookup)
    have hnm := nodup_take_not_mem (fun s => (s.ID' : List w8)) ss _ sv (by unfold srvIds at Hnd; exact Hnd) Hsv_lookup
    have hnm2 : sv.Address' ∉ (ss.take (sint.nat k)).map (fun s => s.Address') := by
      have e : (ss.take (sint.nat k)).map (fun s => s.Address') =
          (ss.take (sint.nat k)).map (fun s => (s.ID' : List w8)) := by
        apply List.map_congr_left
        intro s hs
        exact (Hsrv s (List.mem_of_mem_take hs)).1
      rw [e, hadr]; exact hnm
    wp_if_destruct
    · exfalso; exact hid Hif
    wp_if_destruct
    · exfalso; rw [hadr] at Hif; exact hid Hif
    wp_apply (wp_map_lookup1 (K := GoString) (V := Bool)) $$ [$Hmid] as Hmid
    rw [keySet_lookup_none _ _ _ hnm, Option.getD_none, show zero_val Bool = false from rfl]
    wp_auto
    wp_apply (wp_mapInsert (K := GoString) (V := Bool)) $$ [$Hmid] as Hmid
    wp_apply (wp_map_lookup1 (K := GoString) (V := Bool)) $$ [$Hmad] as Hmad
    rw [keySet_lookup_none _ _ _ hnm2, Option.getD_none, show zero_val Bool = false from rfl]
    wp_auto
    wp_apply (wp_mapInsert (K := GoString) (V := Bool)) $$ [$Hmad] as Hmad
    have hle := checkConfiguration.srvVoters_take_le ss (sint.nat k)
    have hsucc := checkConfiguration.srvVoters_take_succ ss (sint.nat k) sv Hsv_lookup
    have hkn : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [List.take_succ, Hsv_lookup] at hsucc
    simp only [Option.toList_some] at hsucc
    wp_if_destruct
    · wp_for_post
      iframe
      iexists k + W64 1, sv, v + W64 1
      rw [hkn, List.take_succ, Hsv_lookup]
      simp only [Option.toList_some, keySet_snoc]
      iframe
      ipureintro; refine ⟨by word, by word, ?_⟩
      rw [hsucc, if_pos Hif, Hk.2.2]; word
    · wp_for_post
      iframe
      iexists k + W64 1, sv, v
      rw [hkn, List.take_succ, Hsv_lookup]
      simp only [Option.toList_some, keySet_snoc]
      iframe
      ipureintro; refine ⟨by word, by word, ?_⟩
      rw [hsucc, if_neg Hif, Nat.add_zero, Hk.2.2]
  · have hk : sint.nat k = ss.length := by word
    have hvk := Hk.2.2
    rw [hk, List.take_length] at hvk
    subst hvk
    have hle := checkConfiguration.srvVoters_take_le ss ss.length
    rw [List.take_length] at hle
    wp_if_destruct
    · have h0 : (srvVoters ss).length = 0 := by word
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.any)
        [interface.mkOk Configuration.ty #c]
      wp_auto
      isplitl []; · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_auto
      wp_apply (wp_Errorf_cfgErr _ c dq ss) $$ [$Hasl $Hs] as %e2 ⟨Hs, #He2⟩
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact List.length_eq_zero_iff.mp h0
      isplitl
      · unfold errOk
        iexists _
        isplitr
        · ipureintro; rfl
        imodintro
        iintro %Ψ HΨ
        iapply He2
        inext
        iexact HΨ
      · ipureintro; exact ⟨e2, rfl⟩
    · iapply HΦ
      iframe
      ileft
      ipureintro
      refine ⟨rfl, fun h => ?_⟩
      rw [h] at Hif
      exact Hif rfl
  /- stage-3 proof:
  := by
  intro c ss dq
  wp_start as ⟨Hs, %Hok⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %mid Hmid
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %mad Hmad
  obtain ⟨Hsrv, Hnd, Hne⟩ := Hok
  ihave HI : (∃ (k : w64) (sv0 : Server) (v : w64),
      "i" ∷ i_ptr ↦ k ∗ "server" ∷ server_ptr ↦ sv0 ∗ "voters" ∷ voters_ptr ↦ v ∗
      "Hmid" ∷ mid ↦$ keySet (fun s => s.ID') (ss.take (sint.nat k)) ∗
      "Hmad" ∷ mad ↦$ keySet (fun s => s.Address') (ss.take (sint.nat k)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z c.Servers'.len ∧ v = k⌝ : IProp GF)
      $$ [i server voters Hmid Hmad]
  · iexists W64 0, _, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · rw [if_pos (by word)]
    list_elem ss (sint.nat k) as sv
    wp_apply (wp_load_slice_index c.Servers' (sint.Z k) ss dq sv Hk.1) $$ [$Hs] as Hs
    · ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact Hsv_lookup
    obtain ⟨hsuf, hadr, hid⟩ := Hsrv sv (List.mem_of_getElem? Hsv_lookup)
    have hnm := nodup_take_not_mem (fun s => (s.ID' : List w8)) ss _ sv (by unfold srvIds at Hnd; exact Hnd) Hsv_lookup
    have hnm2 : sv.Address' ∉ (ss.take (sint.nat k)).map (fun s => s.Address') := by
      have e : (ss.take (sint.nat k)).map (fun s => s.Address') =
          (ss.take (sint.nat k)).map (fun s => (s.ID' : List w8)) := by
        apply List.map_congr_left
        intro s hs
        exact (Hsrv s (List.mem_of_mem_take hs)).2.1
      rw [e, hadr]; exact hnm
    wp_if_destruct
    · exfalso; exact hid Hif
    wp_if_destruct
    · exfalso; rw [hadr] at Hif; exact hid Hif
    wp_apply (wp_map_lookup1 (K := GoString) (V := Bool)) $$ [$Hmid] as Hmid
    rw [keySet_lookup_none _ _ _ hnm, Option.getD_none, show zero_val Bool = false from rfl]
    wp_auto
    wp_apply (wp_mapInsert (K := GoString) (V := Bool)) $$ [$Hmid] as Hmid
    wp_apply (wp_map_lookup1 (K := GoString) (V := Bool)) $$ [$Hmad] as Hmad
    rw [keySet_lookup_none _ _ _ hnm2, Option.getD_none, show zero_val Bool = false from rfl]
    wp_auto
    wp_apply (wp_mapInsert (K := GoString) (V := Bool)) $$ [$Hmad] as Hmad
    rw [decide_eq_true hsuf]
    wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, sv, v + W64 1
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_succ, Hsv_lookup]
    simp only [Option.toList_some, keySet_snoc]
    iframe
    ipureintro; refine ⟨by word, by word, by rw [Hk.2.2]⟩
  · wp_if_destruct
    · exfalso
      have hvk := Hk.2.2
      subst hvk
      have : ss.length = 0 := by word
      exact Hne (List.length_eq_zero_iff.mp this)
    iapply HΦ
    iframe
  -/

end proof

end Perennial
