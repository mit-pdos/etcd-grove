/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__pickServer.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).pickServer` (stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__pickServer
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Futures
public import Perennial.Spec.sync.atomic.LoadUint64

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

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 2000000 in
theorem github_com.hashicorp.raft.Raft.pickServer.wp_proof
    (wp_LoadUint64 : sync.atomic.LoadUint64.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.pickServer.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T ccfg cfg cidx li ss rs rmap => by
  wp_start as ⟨#Hr, Hconf, #Hcfg, Hrs, Hrsm, #Hshared⟩
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, -, -, -, -⟩
  unfold cfgVal
  icases Hcfg with ⟨#Hss, %Hssok⟩
  wp_auto
  ihave %Hsslen := ownSlice_len $$ Hss
  obtain ⟨-, -, Hssv, -, -⟩ := Hssok
  ihave HI : (∃ (k : Nat) (sv : Server) (cur : w64) (p : Loc),
      "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv ∗ "current" ∷ current_ptr ↦ cur ∗
      "pick" ∷ pick_ptr ↦ p ∗ "%Hk" ∷ ⌜k ≤ ss.length⌝ ∗
      "Hp" ∷ (⌜p = null⌝ ∨ ∃ (j : SID) (s : Loc), p ↦ voterSrv j ∗
        ⌜rmap !! j = some s ∧ j ≠ i ∧ j ∈ srvVoters ss⌝) : IProp GF)
    $$ [i server current pick]
  · iexists 0, _, _, _; iframe
    isplitr; · ipureintro; omega
    ileft; ipureintro; rfl
  wp_for HI
  wp_if_destruct
  · have hk : k < ss.length := by word
    have hk63 : k < 2 ^ 63 := by word
    list_elem ss k as sv
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z cfg.Servers'.len from
      ⟨by word, Hif⟩)]
    wp_apply (wp_load_slice_index cfg.Servers' (sint.Z (W64 k)) ss DFrac.discard sv (by word))
      $$ [$Hss] as Hss'
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hsv_lookup
    have hsvmem : sv ∈ ss := List.mem_of_getElem? Hsv_lookup
    obtain ⟨-, hsaddr, -⟩ := Hssv sv hsvmem
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (k + 1), sv, cur, p
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe; ipureintro; omega
    · have hni : sv.ID' ≠ i := Hif
      by_cases hns : ¬ sv.Suffrage' = W64 0
      · rw [decide_eq_false hns]
        wp_auto
        wp_for_post
        iframe
        iexists (k + 1), sv, cur, p
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe; ipureintro; omega
      have hsuf : sv.Suffrage' = W64 0 := Decidable.of_not_not hns
      have hsv : sv = voterSrv sv.ID' := by
        cases sv; simp only at hsuf hsaddr; subst hsuf; subst hsaddr; rfl
      have hvot : (sv.ID' : List w8) ∈ srvVoters ss := by
        unfold srvVoters
        exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hsvmem, decide_eq_true hsuf⟩)
      rw [decide_eq_true hsuf]
      wp_auto
      wp_apply (wp_map_lookup2 ServerID.ty (go.GoType.PointerType followerReplication.ty) rs rmap
        sv.ID' (DFrac.own 1)) $$ [$Hrsm] as Hrsm
      cases hsj : rmap !! sv.ID' with
      | none =>
        simp only [Option.isSome_none, Option.getD_none]
        wp_auto
        wp_for_post
        iframe
        iexists (k + 1), sv, cur, p
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe; ipureintro; omega
      | some sj =>
        simp only [Option.isSome_some, Option.getD_some]
        wp_auto
        ihave #Hsh := BigSepM.bigSepM_lookup hsj $$ Hshared
        ihave #Hni := replShared_nextCell r γ rc i T sv.ID' sj $$ Hsh
        unfold nextCell
        wp_apply (wp_LoadUint64 _ (DFrac.own (1 : Qp).half))
        iinv Hni with ⟨%x, Hx⟩ Hclose
        iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑nextIdxN from Iris.Std.LawfulSet.empty_subset)
        iintro Hmask
        inext
        iexists x
        iframe Hx
        iintro Hx
        imod Hmask
        imod Hclose $$ [Hx]
        · inext; iexists x; iframe
        imodintro
        wp_auto
        wp_if_destruct
        · wp_for_post
          iframe
          iexists (k + 1), sv, x, tmp_ptr
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe
          isplitr; · ipureintro; omega
          iright; iexists sv.ID', sj
          rw [← hsv]
          iframe; ipureintro; exact ⟨hsj, hni, hvot⟩
        · wp_for_post
          iframe
          iexists (k + 1), sv, cur, p
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe; ipureintro; omega
  · iapply HΦ
    iframe
  /- stage-3 proof:
  :=
  fun r γ rc i T ccfg cfg cidx rs rmap => by
  wp_start as ⟨#Hr, Hconf, #Hcfg, Hrs, Hrsm, #Hshared⟩
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, -, -, -, -⟩
  unfold cfgIs
  icases Hcfg with ⟨%ss, #Hss, %Hssok⟩
  wp_auto
  ihave %Hsslen := ownSlice_len $$ Hss
  obtain ⟨Hssid, Hssv, Hssl⟩ := Hssok
  ihave HI : (∃ (k : Nat) (sv : Server) (cur : w64) (p : Loc),
      "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv ∗ "current" ∷ current_ptr ↦ cur ∗
      "pick" ∷ pick_ptr ↦ p ∗ "%Hk" ∷ ⌜k ≤ ss.length⌝ ∗
      "Hp" ∷ (⌜p = null⌝ ∨ ∃ (j : SID) (s : Loc), p ↦ voterSrv j ∗ ⌜rmap !! j = some s⌝) : IProp GF)
    $$ [i server current pick]
  · iexists 0, _, _, _; iframe
    isplitr; · ipureintro; omega
    ileft; ipureintro; rfl
  wp_for HI
  wp_if_destruct
  · have hk : k < ss.length := by word
    have hk63 : k < 2 ^ 63 := by word
    list_elem ss k as sv
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z cfg.Servers'.len from
      ⟨by word, Hif⟩)]
    wp_apply (wp_load_slice_index cfg.Servers' (sint.Z (W64 k)) ss DFrac.discard sv (by word))
      $$ [$Hss] as Hss'
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hsv_lookup
    have hsvmem : sv ∈ ss := List.mem_of_getElem? Hsv_lookup
    obtain ⟨hsuf, hsaddr, hsne⟩ := Hssv sv hsvmem
    have hsv : sv = voterSrv sv.ID' := by
      cases sv; simp only at hsuf hsaddr; subst hsuf; subst hsaddr; rfl
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (k + 1), sv, cur, p
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe; ipureintro; omega
    · rw [decide_eq_true hsuf]
      wp_auto
      wp_apply (wp_map_lookup2 ServerID.ty (go.GoType.PointerType followerReplication.ty) rs rmap
        sv.ID' (DFrac.own 1)) $$ [$Hrsm] as Hrsm
      cases hsj : rmap !! sv.ID' with
      | none =>
        simp only [Option.isSome_none, Option.getD_none]
        wp_auto
        wp_for_post
        iframe
        iexists (k + 1), sv, cur, p
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe; ipureintro; omega
      | some sj =>
        simp only [Option.isSome_some, Option.getD_some]
        wp_auto
        ihave #Hsh := BigSepM.bigSepM_lookup hsj $$ Hshared
        ihave #Hni := replShared_nextCell r γ rc i T sv.ID' sj $$ Hsh
        unfold nextCell
        wp_apply (wp_LoadUint64 _ (DFrac.own (1 : Qp).half))
        iinv Hni with ⟨%x, Hx⟩ Hclose
        iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑nextIdxN from Iris.Std.LawfulSet.empty_subset)
        iintro Hmask
        inext
        iexists x
        iframe Hx
        iintro Hx
        imod Hmask
        imod Hclose $$ [Hx]
        · inext; iexists x; iframe
        imodintro
        wp_auto
        wp_if_destruct
        · wp_for_post
          iframe
          iexists (k + 1), sv, x, tmp_ptr
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe
          isplitr; · ipureintro; omega
          iright; iexists sv.ID', sj
          rw [← hsv]
          iframe; ipureintro; exact hsj
        · wp_for_post
          iframe
          iexists (k + 1), sv, cur, p
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe; ipureintro; omega
  · iapply HΦ
    iframe
  -/

end proof

end Perennial
