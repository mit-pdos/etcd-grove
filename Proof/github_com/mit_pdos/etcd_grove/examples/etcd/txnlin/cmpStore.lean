/-
Lean-first (no Rocq counterpart).

The proof of `cmpStore`: the revisions, the lengths, then the loop's invariant is that the
entries before the index are equal (`compareLex_at`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStore
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStr
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpVR

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

theorem cmpStore.wp_proof (wp_cmpInt : cmpInt.spec (GF := GF) (hG := hG))
    (wp_cmpStr : cmpStr.spec (GF := GF) (hG := hG)) (wp_cmpVR : cmpVR.spec (GF := GF) (hG := hG)) :
    cmpStore.spec (GF := GF) (hG := hG) := by
  intro a b ga gb
  wp_start as ⟨#Ha, #Hb⟩
  unfold storeOwn
  icases Ha with ⟨#Hak, %Har⟩
  icases Hb with ⟨#Hbk, %Hbr⟩
  ihave %Hla := ownSlice_len $$ Hak
  ihave %Hlb := ownSlice_len $$ Hbk
  simp only [cmpStO, cmpLenLex, compareLex, cmpOn]
  rw [← Har, ← Hbr,
    show cmpZ ga.kvs.length gb.kvs.length = cmpW a.kvs'.len b.kvs'.len by
      simp only [cmpW]; congr 1 <;> word]
  (try wp_auto)
  wp_apply wp_cmpInt
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  (try wp_auto)
  wp_apply wp_cmpInt
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  (try wp_auto)
  have Heq : a.kvs'.len = b.kvs'.len :=
    Std.LawfulEqCmp.eq_of_compare (cmp := cmpW) ((ordW_eq_zero _).1 Hif)
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
    have hcl := compareLex_at (cmp := cmpEntO) ga.kvs gb.kvs (sint.nat i) w w2 Hi.2.2 Hw_lookup
      Hw2_lookup
    rw [show cmpEntO w w2 = (cmpS w.key' w2.key').then (cmpVRO w.r' w2.r') from rfl,
      Ordering.then_assoc] at hcl
    ihave Hw := (ownSlice_elem_acc (sint.Z i) w a.kvs' DFrac.discard ga.kvs Hi.1 Hw_lookup) $$ Hak
    icases Hw with ⟨#Hw, -⟩
    ihave Hwf := entry_fields_disc _ w $$ Hw
    icases Hwf with ⟨#Hwk, #Hwr⟩
    ihave Hw2 := (ownSlice_elem_acc (sint.Z i) w2 b.kvs' DFrac.discard gb.kvs Hi.1 Hw2_lookup) $$ Hbk
    icases Hw2 with ⟨#Hw2, -⟩
    ihave Hwf2 := entry_fields_disc _ w2 $$ Hw2
    icases Hwf2 with ⟨#Hwk2, #Hwr2⟩
    simp only [Hb'.1, Hif, true_and, ↓reduceIte]
    wp_auto
    simp only [Hb'.1, Hif, true_and, ↓reduceIte]
    wp_auto
    simp only [Hb2', _root_.and_self, ↓reduceIte]
    wp_auto
    wp_apply wp_cmpStr
    wp_if_destruct
    · have Hk := Hif; clear Hif
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_auto
      simp only [Hb2', _root_.and_self, ↓reduceIte]
      wp_auto
      wp_apply wp_cmpVR
      wp_if_destruct
      · have hw : w = w2 := by
          have e1 := Std.LawfulEqCmp.eq_of_compare (cmp := cmpS) ((ordW_eq_zero _).1 Hk)
          have e2 := Std.LawfulEqCmp.eq_of_compare (cmp := cmpVRO) ((ordW_eq_zero _).1 Hif)
          cases w; cases w2; simp_all
        wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
          List.take_add_one, Hi.2.2, Hw_lookup, Hw2_lookup, hw]
      · wp_for_post
        rw [hcl, then_of_eq _ Hk, then_of_ne _ Hif]
        iapply HΦ; itrivial
    · wp_for_post
      rw [hcl, then_of_ne _ Hif]
      iapply HΦ; itrivial
  · have h1 : ga.kvs.length = sint.nat i := by word
    have h2 : gb.kvs.length = sint.nat i := by rw [Hlb.1, ← Heq]; word
    have heq : ga.kvs = gb.kvs := by
      have := Hi.2.2
      rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
    rw [heq, Std.ReflCmp.compare_self (cmp := List.compareLex cmpEntO)]
    dsimp only [ordW]
    iapply HΦ; itrivial

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
