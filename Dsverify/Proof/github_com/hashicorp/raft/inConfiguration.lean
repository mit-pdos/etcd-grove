/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/inConfiguration.lean (241f27e).
-/
/-
The proof of `raft.inConfiguration`: a scan of the bootstrap configuration's servers (one per
voter, in order).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.inConfiguration

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

open github_com.hashicorp.raft

theorem github_com.hashicorp.raft.inConfiguration.wp_proof :
    github_com.hashicorp.raft.inConfiguration.spec (GF := GF) (hG := hG) :=
  fun c ss dq id => by
  wp_start as Hss
  wp_auto
  ihave %Hsllen := ownSlice_len $$ Hss
  ihave HI : (∃ (k : Nat) (sv : Server),
      "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv ∗
      "%Hk" ∷ ⌜k ≤ ss.length ∧ ∀ s ∈ ss.take k, s.ID' ≠ id⌝ : IProp GF) $$ [i server]
  · iexists 0, _; iframe; ipureintro; simp
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hk, Hnot⟩ := Hk
    have hk : k < ss.length := by word
    list_elem ss k as sk
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index c.Servers' (sint.Z (W64 k)) ss dq sk (by word)) $$ [$Hss] with Hss
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hsk_lookup
    wp_if_destruct
    · wp_for_post
      have hin : (sk.ID' : List w8) ∈ srvIds ss :=
        List.mem_map_of_mem (f := fun s : Server => (s.ID' : List w8))
          (List.mem_of_getElem? Hsk_lookup)
      rw [decide_eq_true hin]
      iapply HΦ; iframe
    · wp_for_post
      iframe
      iexists k + 1, sk
      have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]
      iframe
      ipureintro
      refine ⟨by omega, fun s hs => ?_⟩
      rw [List.take_add_one, Hsk_lookup] at hs
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · exact Hnot s hs
      · exact Hif
  · obtain ⟨Hk, Hnot⟩ := Hk
    have hk : k = ss.length := by word
    subst hk
    rw [List.take_length] at Hnot
    have hnin : (id : List w8) ∉ srvIds ss := by
      unfold srvIds; simp only [List.mem_map, not_exists, not_and]
      intro s hs he; exact Hnot s hs he
    rw [decide_eq_false hnin]
    iapply HΦ; iframe
  /- stage-3 proof:
  :=
  fun γ c id => by
  wp_start as Hc
  unfold cfgIs
  icases Hc with ⟨%ss, #Hss, %Hok⟩
  wp_auto
  ihave %Hsllen := ownSlice_len $$ Hss
  ihave HI : (∃ (k : Nat) (sv : Server),
      "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv ∗
      "%Hk" ∷ ⌜k ≤ ss.length ∧ ∀ s ∈ ss.take k, s.ID' ≠ id⌝ : IProp GF) $$ [i server]
  · iexists 0, _; iframe; ipureintro; simp
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hk, Hnot⟩ := Hk
    have hk : k < ss.length := by word
    list_elem ss k as sk
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index c.Servers' (sint.Z (W64 k)) ss DFrac.discard sk (by word)) $$ [$Hss] with -
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hsk_lookup
    wp_if_destruct
    · wp_for_post
      have hin := List.mem_map_of_mem (f := fun s : Server => (s.ID' : List w8))
        (List.mem_of_getElem? Hsk_lookup)
      rw [Hok.1] at hin
      rw [decide_eq_true hin]
      iapply HΦ; itrivial
    · wp_for_post
      iframe
      iexists k + 1, sk
      have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]
      iframe
      ipureintro
      refine ⟨by omega, fun s hs => ?_⟩
      rw [List.take_add_one, Hsk_lookup] at hs
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · exact Hnot s hs
      · exact Hif
  · obtain ⟨Hk, Hnot⟩ := Hk
    have hk : k = ss.length := by word
    subst hk
    rw [List.take_length] at Hnot
    have hnin : (id : List w8) ∉ γ.srvs := by
      rw [← Hok.1]; simp only [List.mem_map, not_exists, not_and]
      intro s hs he; exact Hnot s hs he
    rw [decide_eq_false hnin]
    iapply HΦ; itrivial
  -/

end proof

end Perennial
