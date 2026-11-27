/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__quorumSize.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).quorumSize`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__quorumSize

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

open github_com.hashicorp.raft proto gprot

/-- (helper) Access to `r.configurations.latest.Servers` in the `configurations` field (any
`latestIndex`; `cfgsServers_acc` of `main/MainCLemmas` fixes it to `1`). -/
theorem Raft.quorumSize.cfgsServers_acc (r : Loc) (ccfg cfg : Configuration) (cidx li : w64)
    (dq : DFrac) :
    (r.[Raft, go!"configurations"] ↦{dq} configurations.mk ccfg cidx cfg li : IProp GF) ⊢
      r.[Raft, go!"configurations"].[configurations, go!"latest"].[Configuration, go!"Servers"] ↦{dq}
        cfg.Servers' ∗
      (r.[Raft, go!"configurations"].[configurations, go!"latest"].[Configuration, go!"Servers"] ↦{dq}
        cfg.Servers' -∗
        r.[Raft, go!"configurations"] ↦{dq} configurations.mk ccfg cidx cfg li) := by
  iintro H
  icases (configurations.configurations_access_load_latest (GF := GF) _
    (configurations.mk ccfg cidx cfg li) dq).access_strict $$ H with ⟨H1, Hc1⟩
  icases (Configuration.Configuration_access_load_Servers (GF := GF) _ cfg dq).access_strict $$ H1
    with ⟨H2, Hc2⟩
  iframe H2
  iintro H2
  iapply Hc1
  iapply Hc2 $$ H2

/-- (helper) The voters of the first `k+1` servers. -/
theorem Raft.quorumSize.srvVoters_take_succ (ss : List Server) (k : Nat) (sk : Server)
    (h : ss[k]? = some sk) :
    (srvVoters (ss.take (k + 1))).length =
      (srvVoters (ss.take k)).length + (if sk.Suffrage' = W64 0 then 1 else 0) := by
  unfold srvVoters
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.filter_append, List.map_append, List.length_append,
    List.filter_cons, List.filter_nil, List.length_map]
  split <;> simp_all

theorem Raft.quorumSize.srvVoters_take_le (ss : List Server) (k : Nat) :
    (srvVoters (ss.take k)).length ≤ k := by
  unfold srvVoters
  rw [List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp [Nat.min_le_left])

theorem github_com.hashicorp.raft.Raft.quorumSize.wp_proof :
    github_com.hashicorp.raft.Raft.quorumSize.spec (GF := GF) (hG := hG) :=
  fun r ccfg cfg cidx li ss dq dq' => by
  wp_start as ⟨Hcfgs, Hss, %Hlt⟩
  icases Raft.quorumSize.cfgsServers_acc r ccfg cfg cidx li dq $$ Hcfgs with ⟨Hsv, Hcl⟩
  wp_auto
  ihave %Hsllen := ownSlice_len $$ Hss
  ihave HI : (∃ k : Nat, "Hctr" ∷ i_ptr ↦ W64 k ∗
      "voters" ∷ voters_ptr ↦ W64 (srvVoters (ss.take k)).length ∗
      "server" ∷ (∃ v : Server, server_ptr ↦ v) ∗
      "%Hk" ∷ ⌜k ≤ ss.length⌝ : IProp GF) $$ [i voters server]
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
    wp_apply (wp_load_slice_index cfg.Servers' (sint.Z (W64 k)) ss dq' sv (by word))
      $$ [$Hss] with Hss
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hsv_lookup
    have hle := Raft.quorumSize.srvVoters_take_le ss k
    have hsucc := Raft.quorumSize.srvVoters_take_succ ss k sv Hsv_lookup
    have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (k + 1)
      rw [hctr]
      have hv : W64 ((srvVoters (List.take k ss)).length : Int) + W64 1 =
          W64 ((srvVoters (List.take (k + 1) ss)).length : Int) := by
        rw [hsucc, if_pos Hif]; word
      rw [hv]
      iframe
      isplitl [server]
      · iexists _; iframe
      ipureintro; omega
    · wp_for_post
      iframe
      iexists (k + 1)
      rw [hctr, hsucc, if_neg Hif, Nat.add_zero]
      iframe
      isplitl [server]
      · iexists _; iframe
      ipureintro; omega
  rename_i Hc
  have hkn : k = ss.length := by simp only [decide_eq_true_eq] at Hc; word
  wp_auto
  subst hkn
  rw [List.take_length]
  ihave Hcfgs := Hcl $$ Hsv
  have hle : (srvVoters ss).length ≤ ss.length := by
    have := Raft.quorumSize.srvVoters_take_le ss ss.length
    rwa [List.take_length] at this
  have hres : BitVec.sdiv (W64 ((srvVoters ss).length : Int)) (W64 2) + W64 1 =
      W64 (((srvVoters ss).length / 2 + 1 : Nat) : Int) := by
    word
  rw [hres]
  iapply HΦ
  iframe
  /- stage-3 proof:
  :=
  fun r γ ccfg cfg cidx dq => by
  wp_start as ⟨Hcfgs, #Hcfg⟩
  unfold cfgIs
  icases Hcfg with ⟨%ss, #Hss, %Hok⟩
  icases cfgsServers_acc r ccfg cfg cidx dq $$ Hcfgs with ⟨Hsv, Hcl⟩
  wp_auto
  ihave %Hsllen := ownSlice_len $$ Hss
  ihave HI : (∃ k : Nat, "Hctr" ∷ i_ptr ↦ W64 k ∗ "voters" ∷ voters_ptr ↦ W64 k ∗
      "server" ∷ (∃ v : Server, server_ptr ↦ v) ∗
      "%Hk" ∷ ⌜k ≤ ss.length⌝ : IProp GF) $$ [i voters server]
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
    have hv := (Hok.2.1 sv (List.mem_of_getElem? Hsv_lookup)).1
    rw [hv]
    wp_auto
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
  subst hkn
  have hlen : γ.srvs.length = ss.length := by rw [← Hok.1, List.length_map]
  ihave Hcfgs := Hcl $$ Hsv
  have hlt : ss.length < 2 ^ 63 := by word
  have hres : BitVec.sdiv (W64 (ss.length : Int)) (W64 2) + W64 1 =
      W64 ((γ.srvs.length / 2 + 1 : Nat) : Int) := by
    rw [hlen]; word
  rw [hres]
  iapply HΦ
  iframe
  ipureintro; omega
  -/

end proof

end Perennial
