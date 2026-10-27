/-
Lean-first (no Rocq counterpart).

The proof of `storeEqual`: the revisions and lengths, then the loop's invariant is that the
entries before the index are equal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.storeEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- An entry's fields, read-only. -/
theorem entry_fields_disc (l : Loc) (v : entry) :
    (l ↦□ v : IProp GF) ⊢ l.[entry, go!"key"] ↦□ v.key' ∗ l.[entry, go!"r"] ↦□ v.r' := by
  iintro #H
  icases (AccessStrict.access_strict (A := l.[entry, go!"key"] ↦□ v.key')
      (A' := l.[entry, go!"key"] ↦□ v.key') (P := l ↦□ v)) $$ H with ⟨H1, -⟩
  icases (AccessStrict.access_strict (A := l.[entry, go!"r"] ↦□ v.r')
      (A' := l.[entry, go!"r"] ↦□ v.r') (P := l ↦□ v)) $$ H with ⟨H2, -⟩
  isplitl [H1]
  · iexact H1
  · iexact H2

theorem storeEqual.wp_proof (wp_vrEqual : vrEqual.spec (GF := GF) (hG := hG)) :
    storeEqual.spec (GF := GF) (hG := hG) := by
  intro a b ga gb
  wp_start as ⟨#Ha, #Hb⟩
  unfold storeOwn
  icases Ha with ⟨#Hak, %Har⟩
  icases Hb with ⟨#Hbk, %Hbr⟩
  ihave %Hla := ownSlice_len $$ Hak
  ihave %Hlb := ownSlice_len $$ Hbk
  wp_auto
  wp_if_destruct
  · have Hrev := Hif; clear Hif
    wp_if_destruct
    · have Heq := Hif; clear Hif
      rename_i iu_ptr
      irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
      ihave HI : (∃ (i j : w64),
          "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.kvs'.len ∧
            ga.kvs.take (sint.nat i) = gb.kvs.take (sint.nat i)⌝ : IProp GF) $$ [i Hiu]
      · iexists W64 0, _
        iframe
        ipureintro; refine ⟨by word, by word, rfl⟩
      wp_for HI
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.kvs'.len := ⟨Hi.1, Hif⟩
        have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.kvs'.len := by rw [← Heq]; exact Hb'
        list_elem ga.kvs (sint.nat i) as w
        list_elem gb.kvs (sint.nat i) as w2
        ihave Hw := (ownSlice_elem_acc (sint.Z i) w a.kvs' DFrac.discard ga.kvs Hi.1 Hw_lookup) $$ Hak
        icases Hw with ⟨#Hw, -⟩
        ihave Hwf := entry_fields_disc _ w $$ Hw
        icases Hwf with ⟨#Hwk, #Hwr⟩
        ihave Hw2 := (ownSlice_elem_acc (sint.Z i) w2 b.kvs' DFrac.discard gb.kvs Hi.1 Hw2_lookup) $$ Hbk
        icases Hw2 with ⟨#Hw2, -⟩
        ihave Hwf2 := entry_fields_disc _ w2 $$ Hw2
        icases Hwf2 with ⟨#Hwk2, #Hwr2⟩
        simp only [Hb', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index a.kvs' (sint.Z i) ga.kvs _ w Hi.1 $$ [Hak] as -
        · isplit
          · iexact Hak
          · ipureintro; exact Hw_lookup
        simp only [Hb', _root_.and_self, ↓reduceIte]
        wp_auto
        simp only [Hb2', _root_.and_self, ↓reduceIte]
        wp_auto
        wp_if_destruct
        · have Hk := Hif
          simp only [Hb', _root_.and_self, ↓reduceIte]
          wp_auto
          simp only [Hb2', _root_.and_self, ↓reduceIte]
          wp_auto
          wp_apply wp_vrEqual w.r' w2.r'
          wp_if_destruct
          · have hw : w = w2 := by cases w; cases w2; simp_all
            wp_for_post
            iframe
            iexists i + W64 1, _
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
              List.take_add_one, Hi.2.2, Hw_lookup, Hw2_lookup, hw]
          · have hne : ga ≠ gb := fun h => Hif (by
              subst h; rw [Hw_lookup] at Hw2_lookup; cases Hw2_lookup; simp)
            wp_for_post
            rw [decide_eq_false hne]
            iapply HΦ; itrivial
        · have hne : ga ≠ gb := fun h => Hif (by
            subst h; rw [Hw_lookup] at Hw2_lookup; cases Hw2_lookup; simp)
          wp_for_post
          rw [decide_eq_false hne]
          iapply HΦ; itrivial
      · have h1 : ga.kvs.length = sint.nat i := by word
        have h2 : gb.kvs.length = sint.nat i := by rw [Hlb.1, ← Heq]; word
        have heq : ga.kvs = gb.kvs := by
          have := Hi.2.2
          rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
        have hst : ga = gb := by
          cases ga; cases gb
          simp only [GSt.mk.injEq] at heq Har Hbr ⊢
          exact ⟨heq, by rw [← Har, ← Hbr, Hrev]⟩
        rw [decide_eq_true hst]
        iapply HΦ; itrivial
    · rw [decide_eq_false (fun h => Hif (by subst h; word))]
      iapply HΦ; itrivial
  · rw [decide_eq_false (fun h => Hif (by rw [Har, Hbr, h]))]
    iapply HΦ; itrivial

end proof

end linkvtxn
end EtcdGrove
end Perennial
