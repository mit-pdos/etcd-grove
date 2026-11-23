/-
`(*Exec).inStack(w)`: whether `w` is on the Tarjan stack.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecSpec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

theorem wp_inStack (e : Loc) (s : GoSlice) (xs : List Loc) (w : Loc) (dq : DFrac) :
    {{ pkgInit_epaxos (GF := GF) ∗ structFieldRef epaxos.Exec go!"stack" e ↦ s ∗ s ↦*{dq} xs }}
      (App (Val (e @!! go.GoType.PointerType epaxos.Exec.ty @!! go!"inStack")) (Val #w))
    {{ RET #(decide (w ∈ xs)); structFieldRef epaxos.Exec go!"stack" e ↦ s ∗ s ↦*{dq} xs }} := by
  wp_start as ⟨Hst, Hs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave HI : (∃ k : w64, "Hi" ∷ i_ptr ↦ k ∗ "Hu" ∷ (∃ u : Loc, u_ptr ↦ u) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ xs.length ∧ w ∉ xs.take (sint.nat k)⌝ : IProp GF)
      $$ [«i» u]
  · iexists W64 0; iframe «i»
    isplitl [u]
    · iexists _; iexact u
    ipureintro; refine ⟨by decide, by simp, by rw [show sint.nat (W64 0) = 0 by rfl]; simp⟩
  wp_for HI
  wp_if_destruct
  · have hkl : sint.nat k < xs.length := by have := Hlen.1; word
    obtain ⟨x, hx⟩ : ∃ x, xs[sint.nat k]? = some x := ⟨xs[sint.nat k], List.getElem?_eq_getElem hkl⟩
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s.len := ⟨Hk.1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z k) xs _ x hb.1 $$ [$Hs] as Hs
    · ipureintro; exact hx
    icases Hu with ⟨%u, Hu⟩
    wp_auto
    wp_if_destruct
    · wp_for_post
      have hmem : w ∈ xs := by rw [Hif]; exact List.mem_of_getElem? hx
      irevert HΦ
      rw [show decide (w ∈ xs) = true from decide_eq_true hmem]
      iintro HΦ
      iapply HΦ
      iframe
    · wp_for_post
      iframe
      iexists k + W64 1
      iframe Hi
      isplitl [Hu]
      · iexists x; iexact Hu
      ipureintro
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by have := Hlen.1; word
      refine ⟨by word, by omega, ?_⟩
      rw [hk1, List.take_add_one, hx]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hk.2.2, Hif⟩
  · have hk : sint.nat k = xs.length := by have := Hlen.1; have := Hk.2.1; word
    have : w ∉ xs := by have := Hk.2.2; rw [hk, List.take_length] at this; exact this
    irevert HΦ
    rw [show decide (w ∈ xs) = false from decide_eq_false this]
    iintro HΦ
    iapply HΦ
    iframe

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
