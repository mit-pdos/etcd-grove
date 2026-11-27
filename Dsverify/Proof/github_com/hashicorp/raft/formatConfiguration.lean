/-
The proof of `raft.formatConfiguration`. Lean-first.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.formatConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.formatServer
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
theorem github_com.hashicorp.raft.formatConfiguration.wp_proof
    (wp_formatServer : github_com.hashicorp.raft.formatServer.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.formatConfiguration.spec (GF := GF) (hG := hG) := by
  intro c ss dq
  wp_start as Hss
  wp_auto
  rename_i ui_ptr
  irename: (ui_ptr ↦ (zero_val w64 : w64)) => Hui
  ihave %Hsllen := ownSlice_len $$ Hss
  ihave HI : (∃ (j u : w64) (sv : Server) (str : GoString),
      "i" ∷ i_ptr ↦ j ∗ "Hui" ∷ ui_ptr ↦ u ∗ "server" ∷ server_ptr ↦ sv ∗ "s" ∷ s_ptr ↦ str ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z c.Servers'.len⌝ : IProp GF) $$ [i Hui server s]
  · iexists W64 0, _, _, _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    list_elem ss (sint.nat j) as sk
    wp_apply (wp_load_slice_index c.Servers' (sint.Z j) ss dq sk (by word)) $$ [$Hss] with Hss
    · ipureintro
      rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hsk_lookup
    wp_if_destruct <;> (
      wp_apply wp_formatServer as %fs -
      wp_for_post
      iframe
      iexists j + W64 1, _, _, _
      iframe
      ipureintro; word)
  · iapply HΦ
    iframe

end proof

end Perennial
