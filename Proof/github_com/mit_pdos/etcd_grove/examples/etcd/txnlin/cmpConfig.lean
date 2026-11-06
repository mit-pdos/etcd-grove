/-
Lean-first (no Rocq counterpart).

The proof of `cmpConfig`: the stores, the lengths, then the loop's invariant is that the
pending inputs before the index are equal (`compareLex_at`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStore
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInput

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

theorem cmpConfig.wp_proof (wp_cmpStore : cmpStore.spec (GF := GF) (hG := hG))
    (wp_cmpInt : cmpInt.spec (GF := GF) (hG := hG))
    (wp_cmpInput : cmpInput.spec (GF := GF) (hG := hG)) :
    cmpConfig.spec (GF := GF) (hG := hG) := by
  intro a b ga gb
  wp_start as ⟨#Ha, #Hb⟩
  unfold cfgOwn
  icases Ha with ⟨#Hast, #Hap⟩
  icases Hb with ⟨#Hbst, #Hbp⟩
  ihave %Hla := ownSlice_len $$ Hap
  ihave %Hlb := ownSlice_len $$ Hbp
  simp only [cmpCfgO, cmpLenLex, compareLex, cmpOn]
  rw [show cmpZ ga.pend.length gb.pend.length = cmpW a.pend'.len b.pend'.len by
      simp only [cmpW]; congr 1 <;> word]
  wp_auto
  wp_apply wp_cmpStore a.st' b.st' ga.st gb.st $$ [$Hast $Hbst]
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  (try wp_auto)
  wp_apply wp_cmpInt
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  (try wp_auto)
  have Heq : a.pend'.len = b.pend'.len :=
    Std.LawfulEqCmp.eq_of_compare (cmp := cmpW) ((ordW_eq_zero _).1 Hif)
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
  ihave HI : (∃ (i j : w64),
      "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.pend'.len ∧
        ga.pend.take (sint.nat i) = gb.pend.take (sint.nat i)⌝ : IProp GF) $$ [i Hiu]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.pend'.len := ⟨Hi.1, Hif⟩
    have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.pend'.len := by rw [← Heq]; exact Hb'
    list_elem ga.pend (sint.nat i) as w
    list_elem gb.pend (sint.nat i) as w2
    have hcl := compareLex_at (cmp := cmpInO) ga.pend gb.pend (sint.nat i) w w2 Hi.2.2 Hw_lookup
      Hw2_lookup
    ihave Hw := (ownSlice_elem_acc (sint.Z i) w a.pend' DFrac.discard ga.pend Hi.1 Hw_lookup) $$ Hap
    icases Hw with ⟨#Hw, -⟩
    ihave Hw2 := (ownSlice_elem_acc (sint.Z i) w2 b.pend' DFrac.discard gb.pend Hi.1 Hw2_lookup) $$ Hbp
    icases Hw2 with ⟨#Hw2, -⟩
    have Hb2 := Hb2'.2
    repeat
      first
        | simp only [Hb'.1, Hif, Hb2, true_and, ↓reduceIte]
        | wp_auto
    wp_apply wp_cmpInput
    wp_if_destruct
    · have hw : w = w2 := Std.LawfulEqCmp.eq_of_compare (cmp := cmpInO) ((ordW_eq_zero _).1 Hif)
      wp_for_post
      iframe
      iexists i + W64 1, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
        List.take_add_one, Hi.2.2, Hw_lookup, Hw2_lookup, hw]
    · wp_for_post
      rw [hcl, then_of_ne _ Hif]
      iapply HΦ; itrivial
  · have h1 : ga.pend.length = sint.nat i := by word
    have h2 : gb.pend.length = sint.nat i := by rw [Hlb.1, ← Heq]; word
    have heq : ga.pend = gb.pend := by
      have := Hi.2.2
      rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
    rw [heq, Std.ReflCmp.compare_self (cmp := List.compareLex cmpInO)]
    dsimp only [ordW]
    iapply HΦ; itrivial

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
