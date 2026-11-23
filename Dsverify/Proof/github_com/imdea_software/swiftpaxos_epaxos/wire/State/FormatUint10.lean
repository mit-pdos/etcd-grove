/-
`state.formatUint10` (FMT-SPRINT's workaround, e7c8041: `Command.String`'s `SCAN` branch): returns
some string, never panics (internal to the state package).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.State

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : StateTreemap GF]

omit [state.Assumptions] in
/-- `a[i] = v'` for a byte array `a` of 20 elements at `p`. -/
theorem wp_store_byte_array20 (p : Loc) (vs : List w8) (i : Int) (v' : w8) (hi : 0 ≤ i ∧ i < 20) :
  {{ (p ↦ (array.mk 20 vs : GoArray w8 20) : IProp GF) }}
    (App (Val (GoInstruction (GoStore go.byte))) (Val (PairV #(arrayIndexRef w8 i p) #v')))
  {{ RET #(); p ↦ (array.mk 20 (vs.set i.toNat v') : GoArray w8 20) }} := by
  iintro %Φ Ha HΦ
  ihave %Hl := array_len _ _ _ _ $$ Ha
  have hlt : i.toNat < vs.length := by omega
  icases array_acc p i _ 20 (array.mk 20 vs) vs[i.toNat] hi.1
    (List.getElem?_eq_getElem hlt) $$ Ha with ⟨Hv, Ha⟩
  wp_apply IntoValTyped.wp_store (t := go.byte) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Ha $$ Hv

theorem state.formatUint10.spec_holds (x : w64) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state }}
    (App (Val (@! state.formatUint10)) (Val #x))
  {{ (s : GoString), RET #s; True }} := by
  wp_start
  wp_auto
  have hz : (zero_val (GoArray w8 20)) = array.mk 20 (List.replicate 20 (W8 0)) := rfl
  rw [hz]
  ihave HI : (∃ (u : w64) (j : w64) (vs : List w8),
      "u" ∷ u_ptr ↦ u ∗ "j" ∷ j_ptr ↦ j ∗ "a" ∷ a_ptr ↦ (array.mk 20 vs : GoArray w8 20) ∗
      "%Hj" ∷ ⌜1 ≤ sint.Z j ∧ sint.Z j ≤ 20 ∧ uint.nat u < 10 ^ (sint.Z j).toNat⌝ :
      IProp GF) $$ [u j a]
  · iexists x, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    have : (sint.Z (W64 20)).toNat = 20 := by word
    rw [this]
    have := x.isLt
    simp only [uint.nat]
    omega
  wp_for HI
  wp_if_destruct
  · have hu10 : 10 ≤ uint.nat u := by word
    have hj2 : 2 ≤ sint.Z j := by
      rcases (show sint.Z j = 1 ∨ 2 ≤ sint.Z j by omega) with h | h
      · rw [h] at Hj; simp at Hj; omega
      · exact h
    have hj1 : sint.Z (j - W64 1) = sint.Z j - 1 := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    wp_apply wp_store_byte_array20 a_ptr vs _ _ (by omega) $$ [$a] as a
    wp_for_post
    iframe
    iexists u / W64 10, j - W64 1, _
    iframe
    ipureintro
    have hd : uint.nat (u / W64 10) = uint.nat u / 10 := by
      simp [uint.nat, BitVec.toNat_udiv]
    have he : (sint.Z (j - W64 1)).toNat = (sint.Z j).toNat - 1 := by omega
    refine ⟨by omega, by omega, ?_⟩
    rw [hd, he]
    obtain ⟨m, hm⟩ : ∃ m, (sint.Z j).toNat = m + 1 := ⟨(sint.Z j).toNat - 1, by omega⟩
    rw [hm] at Hj ⊢
    rw [Nat.pow_succ] at Hj
    simp only [Nat.add_sub_cancel]
    omega
  have hj1 : sint.Z (j - W64 1) = sint.Z j - 1 := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  wp_apply wp_store_byte_array20 a_ptr vs _ _ (by omega) $$ [$a] as a
  generalize hj' : j - W64 1 = j' at *
  generalize hvs' : vs.set (sint.Z j').toNat _ = vs' at *
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by word, by word⟩)]
  icases (array_split j' a_ptr _ 20 (array.mk 20 vs') ⟨by omega, by omega⟩).1 $$ a with ⟨-, Hsuf⟩
  ihave %Hl := array_len _ _ _ _ $$ Hsuf
  ihave Hsl : slice.mk (arrayIndexRef w8 (sint.Z j') a_ptr) (W64 20 - j') (W64 20 - j') ↦*
      ((array.mk 20 vs' : GoArray w8 20).arr.drop (sint.nat j')) $$ [Hsuf]
  · have e : sint.Z (W64 20 - j') = 20 - sint.Z j' := by word
    rw [ownSlice_unseal]; unfold ownSliceDef
    iright
    dsimp only; rw [e]
    isplitl [Hsuf]
    · iexact Hsuf
    · ipureintro; omega
  wp_apply wp_bytes_to_string _ _ (DFrac.own 1) $$ [$Hsl] as Hsl
  iapply HΦ $$ %_ []
  itrivial

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
