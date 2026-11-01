/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/SetupWrite.lean`: the outer loop's
invariant, no set-up put of a principal visited is the event; the inner loop's, none of the
current principal's prefixes visited. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetupWrite
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Principals
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.keyOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Writer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode common

/-! ## The loops' pure steps -/

section pure
variable [GooseExts]

/-- The event is the set-up put of `x/<w>/d`. -/
def swMatch (e : wev) (x w : GoString) : Prop :=
  e.Put' = true ∧ e.Key' = keyOfK x w go!"d" ∧ e.Val' = go!"setup"

/-- A repeat of a set-up put is the set-up put of some principal and prefix. -/
theorem setupWriteK_iff (e : wev) :
    setupWriteK e.Put' e.Key' e.Val' ↔ ∃ w ∈ principals, ∃ x ∈ keyParts, swMatch e x w := by
  unfold setupWriteK setupPutK setupKeys swMatch
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨hp, ⟨w, hw, x, hx, hk⟩, hv⟩
    exact ⟨w, hw, x, hx, hp, hk.symm, hv⟩
  · rintro ⟨w, hw, x, hx, hp, hk, hv⟩
    exact ⟨hp, ⟨w, hw, x, hx, hk.symm⟩, hv⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem SetupWrite.wp_proof (wp_Principals : Principals.spec (GF := GF) (hG := hG))
    (wp_keyOf : keyOf.spec (GF := GF) (hG := hG)) :
    SetupWrite.spec (GF := GF) (hG := hG) := by
  intro e
  wp_start
  wp_auto
  wp_apply wp_Principals as %psl Hpsl
  ihave %Hpl := ownSlice_len $$ Hpsl
  ihave HI : (∃ (j : w64) (w0 : GoString),
      "i" ∷ i_ptr ↦ j ∗ "who" ∷ who_ptr ↦ w0 ∗ "Hpsl" ∷ psl ↦* principals ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z psl.len⌝ ∗
      "%Hno" ∷ ⌜∀ w ∈ principals.take (sint.nat j), ∀ x ∈ keyParts, ¬ swMatch e x w⌝ : IProp GF)
      $$ [i who Hpsl]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    rw [show sint.nat (W64 0) = 0 by word]
    simp
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z psl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem principals (sint.nat j) as w
    have hwm : w ∈ principals := List.mem_of_getElem? Hw_lookup
    wp_apply wp_load_slice_index psl (sint.Z j) principals (DFrac.own 1) w Hj.1 $$ [Hpsl] as Hpsl
    · iframe; ipureintro; exact Hw_lookup
    (try wp_auto)
    wp_apply wp_slice_literal (V := GoString) keyParts
    isplitr
    · ipureintro; rfl
    iintro %xsl ⟨Hxsl, -⟩
    simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
      show max (max (2 : Int) 0) 0 = 2 from rfl]
    (try wp_auto)
    ihave HJ : (∃ (n : w64) (x0 : GoString),
        "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ x0 ∗ "Hxsl" ∷ _ ↦* keyParts ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2⌝ ∗
        "%Hnx" ∷ ⌜∀ x ∈ keyParts.take (sint.nat n), ¬ swMatch e x w⌝ : IProp GF)
        $$ [i x Hxsl]
    · iexists W64 0, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [show sint.nat (W64 0) = 0 by word]
      simp
    wp_for HJ
    wp_if_destruct
    · have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨Hn.1, Hif⟩
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      have Hnk : sint.nat n < keyParts.length := by rw [show keyParts.length = 2 from rfl]; word
      list_elem keyParts (sint.nat n) as x
      have hxm : x ∈ keyParts := List.mem_of_getElem? Hx_lookup
      have Hns : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      wp_apply wp_load_slice_index _ (sint.Z n) keyParts (DFrac.own 1) x Hn.1 $$ [Hxsl] as Hxsl
      · iframe; ipureintro; exact Hx_lookup
      (try wp_auto)
      generalize hd : decide (setupWriteK e.Put' e.Key' e.Val') = d
      cases hput : e.Put'
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, x
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, ?_⟩
        rw [Hns]
        refine take_mem_succ keyParts _ x Hx_lookup _ Hnx ?_
        intro h; rw [h.1] at hput; cases hput
      · (try wp_auto)
        wp_apply wp_keyOf
        (try wp_auto)
        wp_if_destruct
        · have hkey := Hif
          (try wp_auto)
          wp_if_destruct
          · -- the set-up put of `x/<w>/d`: `true`
            (try wp_auto)
            wp_for_post
            wp_for_post
            have hm : setupWriteK e.Put' e.Key' e.Val' :=
              (setupWriteK_iff e).2 ⟨w, hwm, x, hxm, hput, hkey, Hif⟩
            rw [← hd, decide_eq_true hm]
            iapply HΦ; itrivial
          · (try wp_auto)
            wp_for_post
            iframe
            iexists n + W64 1, x
            iframe
            ipureintro
            refine ⟨⟨by word, by word⟩, ?_⟩
            rw [Hns]
            refine take_mem_succ keyParts _ x Hx_lookup _ Hnx ?_
            intro h; exact Hif h.2.2
        · (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, x
          iframe
          ipureintro
          refine ⟨⟨by word, by word⟩, ?_⟩
          rw [Hns]
          refine take_mem_succ keyParts _ x Hx_lookup _ Hnx ?_
          intro h; exact Hif h.2.1
    · -- no set-up put of `w`: the next principal
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, w
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]
      refine take_mem_succ principals _ w Hw_lookup _ Hno ?_
      have hn2 : sint.nat n = keyParts.length := by
        rw [show keyParts.length = 2 from rfl]; word
      rw [hn2, List.take_length] at Hnx
      exact Hnx
  · -- none: `false`
    (try wp_auto)
    have hj : sint.nat j = principals.length := by word
    rw [hj, List.take_length] at Hno
    have hn : ¬ setupWriteK e.Put' e.Key' e.Val' := by
      rw [setupWriteK_iff]
      rintro ⟨w, hw, x, hx, hm⟩
      exact Hno w hw x hx hm
    rw [decide_eq_false hn]
    iapply HΦ; itrivial

end proof

end authkv
end EtcdGrove
end Perennial
