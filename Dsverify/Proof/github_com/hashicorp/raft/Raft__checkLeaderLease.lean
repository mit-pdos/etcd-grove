/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__checkLeaderLease.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).checkLeaderLease`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__checkLeaderLease
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__quorumSize
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__LastContact
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Sub
public import Perennial.Proof.time.PtrMethods

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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 2000000 in
theorem github_com.hashicorp.raft.Raft.checkLeaderLease.wp_proof
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Sub : time.Time.Sub.spec (GF := GF) (hG := hG))
    (wp_LastContact : github_com.hashicorp.raft.followerReplication.LastContact.spec (GF := GF) (hG := hG))
    (wp_quorumSize : github_com.hashicorp.raft.Raft.quorumSize.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.checkLeaderLease.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s tid => by
  wp_start as ⟨#Hr, Hm, Hl, Htok⟩
  ihave ⟨#HInv, #Hvoter⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, -, -, -, -⟩
  ihave ⟨%ccfg, %cfg, %cidx, %li, Hconf, #Hcfg, #Hccfg, %Hli, Hmback⟩ :=
    mainOwnAt_conf r γ rc i s stLeader $$ Hm
  ihave #Hcfg2 : cfgAtIs γ s.log (lastCfgIdx s.log) cfg $$ []
  · rw [← Hli]; iexact Hcfg
  ihave ⟨%ss, #Hss, %Hssids⟩ := cfgAtIs_ids γ s.log cfg $$ Hcfg2
  unfold leaderOwnC leaderOwnM
  icases Hl with ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, #Hldr', #Hlen0, Hcc, #Hccn, Hcm,
    #Hcmi, Hinfl, Hinfls, Hinflc, %Hfs, Hfs, Hrs, Hrsm, Hrmap, Hnt, HNMp, Hsd, #Hsdn, %Hcov, %pb,
    #Hpb, %Hpbc⟩
  ihave ⟨#Hshared, Hstops⟩ := (replMain_split r γ i s.term rmap).1 $$ Hrmap
  wp_auto
  wp_apply (wp_config r γ rc i) $$ [$Hr] as %c %Hc
  wp_apply wp_Now as %now -
  ihave %Hsslen := ownSlice_len $$ Hss
  ihave HI : (∃ (k : Nat) (cn : w64) (sv : Server) (md : w64),
      "i" ∷ i_ptr ↦ W64 k ∗ "contacted" ∷ contacted_ptr ↦ cn ∗ "server" ∷ server_ptr ↦ sv ∗
      "maxDiff" ∷ maxDiff_ptr ↦ md ∗ "%Hk" ∷ ⌜k ≤ ss.length ∧ uint.nat cn ≤ k⌝ ∗
      "Htok" ∷ rtok tid : IProp GF) $$ [i contacted server maxDiff Htok]
  · iexists 0, _, _, _; iframe; ipureintro; exact ⟨Nat.zero_le _, by word⟩
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hkle, Hcn⟩ := Hk
    have hk : k < ss.length := by word
    have hk63 : k < 2 ^ 63 := by word
    list_elem ss k as sv
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z cfg.Servers'.len from
      ⟨by word, Hif⟩)]
    wp_apply (wp_load_slice_index cfg.Servers' (sint.Z (W64 k)) ss DFrac.discard sv (by word))
      $$ [$Hss] as Hss'
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hsv_lookup
    have hsvmem : sv ∈ ss := List.mem_of_getElem? Hsv_lookup
    have hsvids : (sv.ID' : List w8) ∈ cfgIdsOf γ.srvs s.log := by
      rw [← Hssids]; exact List.mem_map.mpr ⟨sv, hsvmem, rfl⟩
    wp_if_destruct
    rotate_left
    · wp_for_post
      iframe
      iexists (k + 1), cn, sv, _
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe; ipureintro; exact ⟨by omega, by word⟩
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (k + 1), (cn + W64 1), sv, _
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe; ipureintro; exact ⟨by omega, by word⟩
    · obtain ⟨sj, hsj⟩ := Option.isSome_iff_exists.mp ((Hcov sv.ID').2 ⟨hsvids, by
        first | exact Hif | (intro h; exact Hif h) | (intro h; apply Hif; rw [h])⟩)
      wp_apply (wp_map_lookup1 ServerID.ty (go.GoType.PointerType followerReplication.ty) rs rmap
        sv.ID' (DFrac.own 1)) $$ [$Hrsm] as Hrsm
      rw [hsj]
      ihave #Hsh := BigSepM.bigSepM_lookup hsj $$ Hshared
      simp only [Option.getD_some]
      wp_apply (wp_LastContact r γ rc i s.term sv.ID' sj tid) $$ [$Hsh $Htok] as %lct Htok
      wp_apply (time.Time.wp_ptr_Sub_of wp_Sub now_ptr now lct) $$ [$now] as %diff now
      wp_if_destruct
      · wp_if_destruct
        · wp_for_post
          iframe
          iexists (k + 1), (cn + W64 1), sv, _
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe; ipureintro; exact ⟨by omega, by word⟩
        · wp_for_post
          iframe
          iexists (k + 1), (cn + W64 1), sv, _
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe; ipureintro; exact ⟨by omega, by word⟩
      · wp_if_destruct
        · wp_for_post
          iframe
          iexists (k + 1), cn, sv, _
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe; ipureintro; exact ⟨by omega, by word⟩
        · wp_for_post
          iframe
          iexists (k + 1), cn, sv, _
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe; ipureintro; exact ⟨by omega, by word⟩
  · wp_apply (wp_quorumSize r ccfg cfg cidx li ss (DFrac.own 1) DFrac.discard) $$ [$Hconf $Hss]
      as ⟨Hconf, -⟩
    · ipureintro; have := Hsslen; word
    ihave Hm := Hmback $$ Hconf
    wp_if_destruct
    · rw [show (Follower : val) = #stFollower from rfl]
      ihave ⟨Hstv, Hmst⟩ := ml_mainOwnAt_state' r γ rc i s stLeader $$ Hm
      wp_apply (wp_setState r γ rc i stLeader stFollower s tid) $$ [$Hr $Hstv $Htok]
        as ⟨Hstv, -, Htok⟩
      · isplitr; · ipureintro; left; rfl
        iapply ml_obsArg_follower γ i s
      iapply HΦ
      iexists stFollower
      isplitl [Hstv Hmst]
      · iapply Hmst $$ Hstv
        ipureintro; decide
      isplitr; · ipureintro; simp
      isplitr [Htok]
      · ihave Hrmap := (replMain_split r γ i s.term rmap).2 $$ [Hstops]
        · iframe; iframe #
        try unfold leaderOwnC leaderOwnM
        iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0; iframe; iframe #
        ipureintro; exact ⟨Hfs, Hcov, Hpbc⟩
      iexact Htok
    · iapply HΦ
      iexists stLeader
      iframe Hm
      isplitr; · ipureintro; simp
      isplitr [Htok]
      · ihave Hrmap := (replMain_split r γ i s.term rmap).2 $$ [Hstops]
        · iframe; iframe #
        try unfold leaderOwnC leaderOwnM
        iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0; iframe; iframe #
        ipureintro; exact ⟨Hfs, Hcov, Hpbc⟩
      iexact Htok

end proof

end Perennial
