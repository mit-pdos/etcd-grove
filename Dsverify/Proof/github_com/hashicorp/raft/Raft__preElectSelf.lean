/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__preElectSelf.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).preElectSelf` (and of its `askPeer` closure and goroutines).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__preElectSelf
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastEntry
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Perennial.Spec.strings.Contains
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Elect

@[expose] public section

set_option linter.deprecated false

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

theorem chan_start_ok {V : Type} (cap : w64) :
    match (if cap = W64 0 then ChanState.Idle else ChanState.Buffered ([] : List V)) with
    | .Idle | .Buffered [] => True | _ => False := by
  by_cases h : cap = W64 0
  · rw [if_pos h]; trivial
  · rw [if_neg h]; trivial

set_option maxHeartbeats 1000000 in
theorem github_com.hashicorp.raft.Raft.preElectSelf.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastEntry : github_com.hashicorp.raft.raftState.getLastEntry.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_Contains : strings.Contains.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.preElectSelf.spec (GF := GF) (hG := hG) :=
  fun r γ rc sid s st tid => by
  wp_start as ⟨#Hr, Hmain, Htok⟩
  ihave #Himm := isRaft_imm r γ rc sid $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #Hlid, -⟩
  ihave #Hif := isRaft_ifaces r γ rc sid $$ Hr
  unfold raftIfaces
  icases Hif with ⟨%logsI, %stableI, %snapsI, %x, %fsmI, %rpcCh, %eof, -, -, -, -, -, -, -, -, #Htr, #Ht,
    %htyp, -⟩
  ihave ⟨#HI, #Hvi⟩ := isRaft_proto r γ rc sid $$ Hr
  ihave #Htc := isRaft_termCell r γ rc sid $$ Hr
  unfold mainOwnAt
  icases Hmain with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %cmp, Hsrv, Hdur, HS, %Hvm, Hll, Hst, Hldr,
    Hpend, Hvreg, Hap, %Hale, Hprod, Hpnd, Hcomp, %Hcmp, Hcfgs, #Hcfg, #Hccfg, %Hcc, #Hcmt, #Hlch, #Hlchan, Hlown, %Hcap⟩
  icases cfgAtIs_srvs γ s.log _ cfg $$ Hcfg with ⟨%ss, #Hss, %Hok⟩
  ihave %Hsllen := ownSlice_len $$ Hss
  have Hssl : ss.length < 2 ^ 32 := Hok.2.1
  icases cfgsServers_acc' r ccfg cfg cidx li (DFrac.own 1) $$ Hcfgs with ⟨Hsv, Hcl⟩
  wp_auto
  simp only [htyp, if_true]
  wp_auto
  have hcap : sint.Z cfg.Servers'.len < 2 ^ 32 := by
    have := Hok.2.1; have := Hsllen; word
  wp_apply (chan.wp_make2 (V := Loc) cfg.Servers'.len) with %ch %γch ⟨#Hch, %Hγcap, Hoch⟩
  · ipureintro; constructor <;> word
  imod start_bag (pvP γ (s.term + 1)) _ ch γch (chan_start_ok _) $$ Hch Hoch with #Hbag
  imod srvOwn_facts γ ⊤ (by solve_ndisj) sid s $$ [HI Hsrv] with ⟨Hsrv, -, %Hsf⟩
  · iframe; iexact HI
  wp_apply (wp_getCurrentTerm.1 r γ sid s) $$ [$HI $Htc $Hsrv] with Hsrv
  wp_apply (wp_getLastEntry r γ rc sid s a) $$ [$Hr $Hll $Hsrv $Hap] with %lli %lt ⟨%Hlilt, Hll, Hsrv, Hap⟩
  · ipureintro; exact Hale.1
  wp_apply (wp_getRPCHeader r γ rc sid) $$ [$Hr] with %hdr #Hhdr
  ipersist r
  ipersist prevoteTrans
  ipersist respCh
  generalize «$r0_ptr» = rqp at *
  irename «$r0» => Hrqfull
  ipersist Hrqfull
  ihave #Hrq := Hrqfull
  iStructNamedPrefix Hrq "rq_"
  ipersist req
  ipersist askPeer
  ihave HI : (∃ k : Nat, "Hctr" ∷ i_ptr ↦ W64 k ∗ "server" ∷ (∃ v : Server, server_ptr ↦ v) ∗
      "%Hk" ∷ ⌜k ≤ ss.length⌝ : IProp GF) $$ [i server]
  · iexists 0; iframe
    isplitl [server]
    · iexists _; iexact server
    ipureintro; omega
  wp_for HI
  split
  · rename_i Hc
    icases server with ⟨%sv0, server⟩
    have hk : k < ss.length := by simp only [decide_eq_true_eq] at Hc; word
    list_elem ss k as sv
    wp_auto
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index cfg.Servers' (sint.Z (W64 k)) ss DFrac.discard sv (by word))
      $$ [$Hss] with -
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hsv_lookup
    have hsv_mem := List.mem_of_getElem? Hsv_lookup
    have hsv := Hok.1 sv hsv_mem
    wp_if_destruct
    rotate_left
    · -- not a voter: skipped
      wp_for_post
      iframe
      iexists (k + 1)
      have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]
      iframe
      isplitl [server]
      · iexists _; iframe
      ipureintro; omega
    wp_if_destruct
    · -- our own pre-vote
      wp_apply (wp_getRPCHeader r γ rc _) $$ [$Hr] with %hdr2 #Hhdr2
      iStructNamed «$v»
      wp_apply (wp_bag_send γch ch «$v_ptr» (pvP γ (s.term + 1))) $$ [$Hbag RequestPreVoteResponse]
      · unfold pvP
        iexists _
        iframe
        ileft; ipureintro
        simp only
        have := Hsf.2.2.2.2.2.1
        word
      wp_for_post
      iframe
      iexists (k + 1)
      have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]
      iframe
      isplitl [server]
      · iexists _; iframe
      ipureintro; omega
    · -- ask another voter
      have hj : sv.ID' ∈ γ.srvs := hsv.1
      imod isSrv_of_mem γ ⊤ (by solve_ndisj) sv.ID' hj $$ HI with #Hvj
      wp_apply (wp_goFunc r γ rc sid) $$ [$Hr $Htok peer] with Htok
      · iintro %tid' Htok
        wp_pures
        wp_auto
        iStructNamed «$r0»
        unfold isTransport
        icases Ht with ⟨-, -, -, -, -, -, -, -, -, #HRPV, -⟩
        rw [hsv.2]
        wp_apply HRPV $$ [] [] [] [RequestPreVoteResponse] [Htok] with %err Hrqfull2 Htok Hres
        · iexact Hvj
        · iexact Hrqfull
        · unfold pvReq
          isplitl
          · ipureintro; exact (rfl : uint.nat (W64 (s.term : Int) + W64 1) = uint.nat (W64 (s.term : Int) + W64 1))
          iexact Hhdr
        · iexact RequestPreVoteResponse
        · iexact Htok
        icases Hres with (⟨%Hnil, %rp, Hrp, Hpv⟩ | ⟨Hne, %rp, Hrp⟩)
        · subst Hnil
          wp_auto
          wp_apply (wp_bag_send γch ch «$r0_ptr» (pvP γ (s.term + 1))) $$ [$Hbag Hrp Hpv]
          · unfold pvP pvResp
            icases Hpv with ⟨Hpv, -⟩
            iexists _; iframe
            have hT : uint.nat (W64 (s.term : Int) + W64 1) = s.term + 1 := by
              have := Hsf.2.2.2.2.2.1; word
            rw [← hT]; iexact Hpv
          iframe
          ipureintro; rfl
        · unfold errOk
          icases Hne with ⟨%e, %he, #HE⟩
          subst he
          wp_auto
          wp_apply HE as %m
          wp_apply wp_Contains
          have hT : uint.nat (W64 (s.term : Int) + W64 1) = s.term + 1 := by
            have := Hsf.2.2.2.2.2.1; word
          generalize (decide (_ <:+: m) : Bool) = b  -- (port) Perennial's Contains: `decide (substr <:+: s)`
          wp_if_destruct
          all_goals
            wp_apply (wp_bag_send γch ch «$r0_ptr» (pvP γ (s.term + 1))) $$ [$Hbag Hrp]
            · unfold pvP; iexists _; iframe
              ileft; ipureintro; exact hT
            iframe
            ipureintro; rfl
      wp_for_post
      iframe
      iexists (k + 1)
      have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]
      iframe
      isplitl [server]
      · iexists _; iframe
      ipureintro; omega
  rename_i Hc
  have hkn : k = ss.length := by simp only [decide_eq_true_eq] at Hc; word
  wp_auto
  ihave Hcfgs := Hcl $$ Hsv
  iapply HΦ
  iexists γch
  iframe
  iframe #
  ipureintro; exact ⟨Hvm, Hale, Hcmp, Hcc, Hcap⟩

end proof

end Perennial
