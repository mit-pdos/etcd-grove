/-
The proof of `Header.get` (`Net/Spec/net/http/Header__get.lean`).
-/
module

public import Net.Spec.net.http.Header__get

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem Header.get.wp_proof : Header.get.spec (GF := GF) (hG := hG) := by
  intro h dq ms key
  unfold hdrVals
  rcases hk : ms !! key with _ | s
  · wp_start as ⟨Hm, -⟩
    wp_auto
    wp_apply wp_map_lookup1 $$ Hm as Hm
    rw [hk]
    wp_auto
    iapply HΦ
    iframe Hm
    ipureintro; simp
  · wp_start as ⟨Hm, %vs, Hs⟩
    wp_auto
    wp_apply wp_map_lookup1 $$ Hm as Hm
    rw [hk]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    simp only [Option.getD_some]
    rcases vs with _ | ⟨x, vs⟩
    · rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z s.len by simp at Hlen; word)]
      wp_auto
      iapply HΦ
      iframe Hm
      isplitl [Hs]
      · iexists []; iexact Hs
      · ipureintro; simp
    · rw [decide_eq_true (show sint.Z (W64 0) < sint.Z s.len by simp at Hlen; word)]
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := by simp at Hlen; word
      wp_auto
      rw [if_pos hb]
      wp_apply wp_load_slice_index s (sint.Z (W64 0)) _ _ x (by decide) $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ
      iframe Hm
      isplitl [Hs]
      · iexists (x :: vs); iexact Hs
      · ipureintro; simp

end proof

end net.http
end Perennial
