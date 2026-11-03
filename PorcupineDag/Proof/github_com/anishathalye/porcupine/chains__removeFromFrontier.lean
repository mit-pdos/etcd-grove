/- Lean-first (no Rocq counterpart).

`(*chains).removeFromFrontier(c)`: the loop over the frontier, then `wp_slice_delete`.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__removeFromFrontier
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.FrontierLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem chains.removeFromFrontier.wp_proof : chains.removeFromFrontier.spec (GF := GF) (hG := hG) :=
    fun ch cl h cs st c hc hfr hcs => by
  wp_start as Hch
  unfold chainsOwnCl chainsRepr
  icases Hch with ⟨%chV, Hch, %Hcleq, %cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  ihave %Hlen := ownSlice_len $$ Hfr
  ihave %Hwf := ownSlice_wf $$ Hfr
  wp_auto
  rename_i ig_ptr
  irename : (ig_ptr ↦ zero_val w64 : IProp GF) => ig
  ihave HI : (∃ (k vv kk : w64),
      "i" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗ "ig" ∷ ig_ptr ↦ kk ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z chV.frontier'.len ∧
        ∀ j, j < sint.nat k → st.frontier[j]? ≠ some (sint.nat c)⌝ : IProp GF) $$ [i v ig]
  · iexists W64 0, _, _
    iframe
    ipureintro; refine ⟨by word, by word, fun j hj => absurd hj (by word)⟩
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z chV.frontier'.len := ⟨Hk.1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    have hkl : sint.nat k < st.frontier.length := by
      rw [List.length_map] at Hlen; word
    obtain ⟨x, hx⟩ : ∃ x, st.frontier[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem hkl⟩
    have hxm : (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64)))[(sint.Z k).toNat]? =
        some (W64 (x : Int)) := by
      rw [show (sint.Z k).toNat = sint.nat k by word, List.getElem?_map, hx]; rfl
    wp_apply wp_load_slice_index chV.frontier' (sint.Z k) _ _ (W64 (x : Int)) Hk.1 $$ [Hfr] as Hfr
    · iframe; ipureintro; exact hxm
    have hxb : x < cs.length := hfr x (List.mem_of_getElem? hx)
    wp_if_destruct
    · have hxe : sint.nat (W64 (x : Int)) = x := by word
      rw [hxe] at Hk ⊢
      have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧ sint.Z k ≤ sint.Z chV.frontier'.cap := by
        word
      simp only [hb1]
      wp_auto
      have hb2 : 0 ≤ sint.Z (k + W64 1) ∧ sint.Z (k + W64 1) ≤ sint.Z chV.frontier'.len ∧
          sint.Z chV.frontier'.len ≤ sint.Z chV.frontier'.cap := by word
      simp only [hb2]
      wp_apply wp_slice_delete chV.frontier' _ k Hb $$ [$Hfr $Hcap] as %sl ⟨Hfr, Hcap⟩
      wp_for_post
      iapply HΦ
      iexists { chV with frontier' := sl }
      iframe Hch
      isplitr
      · ipureintro; exact Hcleq
      iexists cvs
      iframe
      rw [eraseIdx_map, ← erase_eq_eraseIdx_of hx Hk.2.2]
      iframe
      ipureintro; exact Hcvs
    · wp_for_post
      iframe
      iexists k + W64 1, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (sint.nat k) with h1 | h1
      · exact Hk.2.2 j h1
      · have : j = sint.nat k := by word
        subst this
        rw [hx]
        intro heq
        apply Hif
        simp only [Option.some.injEq] at heq
        subst heq
        word
  · have hne : sint.nat c ∉ st.frontier := by
      intro hm
      obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hm
      exact Hk.2.2 j (by rw [List.length_map] at Hlen; word) (by rw [List.getElem?_eq_getElem hj, hjx])
    rw [List.erase_of_not_mem hne]
    simp
    iapply HΦ
    iexists chV; iframe Hch; isplitr
    · ipureintro; exact Hcleq
    iexists cvs; iframe; ipureintro; exact Hcvs

end proof

end porcupine
end EtcdGrove
end Perennial
