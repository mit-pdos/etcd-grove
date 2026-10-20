/- Lean-first (no Rocq counterpart). The proof of `check`: its two loops, each condition false
by `CheckOk`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.watchkv.check

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.watchkv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions]

theorem check.wp_proof (wp_attempted : attempted.spec (GF := GF) (hG := hG)) :
    check.spec (GF := GF) (hG := hG) := by
  intro esl tsl osl evs tried oks Hok
  obtain ⟨Hlen, Hevs, Hoks⟩ := Hok
  wp_start as ⟨#He, #Ht, #Ho⟩
  ihave %Hel := ownSlice_len $$ He
  ihave %Hol := ownSlice_len $$ Ho
  wp_auto
  rename_i ig
  irename : (ig ↦ zero_val w64 : IProp GF) => gi
  -- the events
  ihave HI : (∃ (j : w64) (e0 : wev) (i0 pv : w64),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "gi" ∷ ig ↦ i0 ∗ "prev" ∷ prev_ptr ↦ pv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z esl.len ∧ (0 < sint.Z j → sint.Z pv = 1 + sint.Z j)⌝ :
      IProp GF) $$ [i e gi prev]
  · iexists W64 0, _, _, _
    iframe
    ipureintro; refine ⟨by word, by word, fun h => by word⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem evs (sint.nat j) as x
    wp_apply wp_load_slice_index esl (sint.Z j) evs DFrac.discard x Hj.1 $$ [He] as -
    · iframe #; ipureintro; exact Hx_lookup
    obtain ⟨hput, hrev, hmem⟩ := Hevs _ x Hx_lookup
    have hjn : sint.Z j + 2 < 2 ^ 63 := by have := Hel.1; word
    rw [hput]
    wp_auto
    wp_if_destruct
    · (try wp_auto)
      wp_if_destruct
      · exfalso; have := Hj.2.2 (by word); word
      (try wp_auto)
      have hxr : x.rev' = j + W64 2 := by
        have : sint.nat j = (sint.Z j).toNat := rfl
        word
      rw [decide_eq_true hxr]
      simp only [Bool.not_true]
      wp_auto
      wp_apply wp_attempted tsl tried DFrac.discard x.key' x.val' as %b ⟨-, %Hb⟩
      · iframe #
      rw [Hb hmem]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, x, j, x.rev'
      iframe
      ipureintro; refine ⟨by word, by word, fun _ => by word⟩
    · (try wp_auto)
      have hxr : x.rev' = j + W64 2 := by
        have : sint.nat j = (sint.Z j).toNat := rfl
        word
      rw [decide_eq_true hxr]
      simp only [Bool.not_true]
      wp_auto
      wp_apply wp_attempted tsl tried DFrac.discard x.key' x.val' as %b ⟨-, %Hb⟩
      · iframe #
      rw [Hb hmem]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, x, j, x.rev'
      iframe
      ipureintro; refine ⟨by word, by word, fun _ => by word⟩
  -- the successful Puts
  (try wp_auto)
  ihave HJ : (∃ (k : w64) (p0 : wrec),
      "i" ∷ i_ptr ↦ k ∗ "p" ∷ p_ptr ↦ p0 ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z osl.len⌝ : IProp GF) $$ [i p]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HJ
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z osl.len := ⟨Hk.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem oks (sint.nat k) as y
    wp_apply wp_load_slice_index osl (sint.Z k) oks DFrac.discard y Hk.1 $$ [Ho] as -
    · iframe #; ipureintro; exact Hy_lookup
    obtain ⟨hr2, e, he, hek, hev⟩ := Hoks y (List.mem_of_getElem? Hy_lookup)
    have hel : (sint.Z y.rev' - 2).toNat < evs.length := (List.getElem?_eq_some_iff.mp he).1
    (try wp_auto)
    wp_if_destruct
    · exfalso; word
    (try wp_auto)
    wp_if_destruct
    · exfalso; have := Hel.1; word
    (try wp_auto)
    have Hb2 : 0 ≤ sint.Z (y.rev' - W64 2) ∧ sint.Z (y.rev' - W64 2) < sint.Z esl.len := by
      have := Hel.1; constructor <;> word
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    have hidx : evs[(sint.Z (y.rev' - W64 2)).toNat]? = some e := by
      rw [show (sint.Z (y.rev' - W64 2)).toNat = (sint.Z y.rev' - 2).toNat by word]; exact he
    wp_apply wp_load_slice_index esl (sint.Z (y.rev' - W64 2)) evs DFrac.discard e Hb2.1 $$ [He] as -
    · iframe #; ipureintro; exact hidx
    (try wp_auto)
    rw [hek]
    simp only [decide_true, Bool.not_true]
    (try wp_auto)
    rw [hev]
    simp only [decide_true, Bool.not_true]
    (try wp_auto)
    wp_for_post
    iframe
    iexists k + W64 1, y
    iframe
    ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end watchkv
end EtcdGrove
end Perennial
