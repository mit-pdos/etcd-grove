module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.storeEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem item_eq_iff (a b : item) : a = b ↔
    a.key' = b.key' ∧ a.obj'.Name' = b.obj'.Name' ∧ a.obj'.Value' = b.obj'.Value' ∧
    a.obj'.ResourceVersion' = b.obj'.ResourceVersion' ∧ a.canon' = b.canon' := by
  obtain ⟨_, ⟨_, _, _⟩, _⟩ := a
  obtain ⟨_, ⟨_, _, _⟩, _⟩ := b
  simp [and_assoc]

theorem storeEqual.wp_proof : storeEqual.spec (GF := GF) (hG := hG) := by
  intro a b ga gb
  wp_start as ⟨#Ha, #Hb⟩
  generalize hd : decide (ga = gb) = res
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
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.items'.len ∧
            ga.items.take (sint.nat i) = gb.items.take (sint.nat i)⌝ : IProp GF) $$ [i Hiu]
      · iexists W64 0, _
        iframe
        ipureintro; refine ⟨by word, by word, rfl⟩
      wp_for HI
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.items'.len := ⟨Hi.1, Hif⟩
        have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.items'.len := by rw [← Heq]; exact Hb'
        list_elem ga.items (sint.nat i) as w
        list_elem gb.items (sint.nat i) as w2
        simp only [Hb', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index a.items' (sint.Z i) ga.items _ w Hi.1 $$ [Hak] as -
        · isplit
          · iexact Hak
          · ipureintro; exact Hw_lookup
        (try simp only [Hif, Hb', _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index a.items' (sint.Z i) ga.items _ w Hi.1 $$ [Hak] as -
        · isplit
          · iexact Hak
          · ipureintro; exact Hw_lookup
        (try simp only [Hb2'.2, Hb2', _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index b.items' (sint.Z i) gb.items _ w2 Hi.1 $$ [Hbk] as -
        · isplit
          · iexact Hbk
          · ipureintro; exact Hw2_lookup
        (try wp_auto)
        repeat' wp_if_destruct
        all_goals first
          | (have hw : w = w2 := by rw [item_eq_iff]; and_intros <;> assumption
             wp_for_post
             iframe
             iexists i + W64 1, _
             iframe
             ipureintro
             refine ⟨by word, by word, ?_⟩
             rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
               List.take_add_one, Hi.2.2, Hw_lookup, Hw2_lookup, hw])
          | (have hne : ga ≠ gb := fun h => by
               subst h; rw [Hw_lookup] at Hw2_lookup; cases Hw2_lookup; simp_all
             wp_for_post
             rw [← hd, decide_eq_false hne]
             iapply HΦ; itrivial)
      · have h1 : ga.items.length = sint.nat i := by word
        have h2 : gb.items.length = sint.nat i := by rw [Hlb.1, ← Heq]; word
        have heq : ga.items = gb.items := by
          have := Hi.2.2
          rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
        have hst : ga = gb := by
          cases ga; cases gb
          simp only [GSt.mk.injEq] at heq Har Hbr ⊢
          exact ⟨heq, by rw [← Har, ← Hbr, Hrev]⟩
        rw [← hd, decide_eq_true hst]
        iapply HΦ; itrivial
    · rw [← hd, decide_eq_false (fun h => Hif (by subst h; word))]
      iapply HΦ; itrivial
  · rw [← hd, decide_eq_false (fun h => Hif (by rw [Har, Hbr, h]))]
    iapply HΦ; itrivial


end proof

end k8setcd3
end EtcdGrove
end Perennial
