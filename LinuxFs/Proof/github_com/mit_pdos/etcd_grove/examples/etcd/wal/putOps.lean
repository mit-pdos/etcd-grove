/- Lean-first (no Rocq counterpart). The proof of `putOps` (W4c U5). -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putOps
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putHS
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putU64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

/-- One more element of a `flatMap` over a prefix. -/
theorem flatMap_take_succ {α β : Type} (l : List α) (f : α → List β) (i : Nat) (x : α)
    (h : l[i]? = some x) : (l.take (i + 1)).flatMap f = (l.take i).flatMap f ++ f x := by
  rw [List.take_add_one, h]; simp

/-- A `flatMap` over the whole list. -/
theorem flatMap_take_length {α β : Type} (l : List α) (f : α → List β) (i : Nat)
    (h : i = l.length) : (l.take i).flatMap f = l.flatMap f := by
  rw [h, List.take_length]

/-- A slice's length as a word. -/
theorem w64_of_length {α : Type} (l : List α) (n : w64) (h : l.length = sint.nat n ∧ 0 ≤ sint.Z n) :
    W64 l.length = n := by
  rw [h.1]; word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem putOps.wp_proof (wp_putU64 : putU64.spec (GF := GF) (hG := hG))
    (wp_putHS : putHS.spec (GF := GF) (hG := hG)) :
    putOps.spec (GF := GF) (hG := hG) := by
  intro b bs s h
  wp_start as ⟨Hb, Hcap, Hr⟩
  iunfold opsRep at Hr
  icases Hr with ⟨%vs, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  wp_auto
  wp_apply wp_putU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  ihave HI : (∃ (i : w64) (bb : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗
      "Hb" ∷ bb ↦* (bs ++ tU64 s.len ++ (h.take (sint.nat i)).flatMap tOpBytes) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗ "h" ∷ h_ptr ↦ s ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i b Hb Hcap h]
  · iexists W64 0, b1
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil,
      List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hil : sint.nat i < vs.length := by
      have : sint.nat i < sint.nat s.len := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, vs[sint.nat i]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨Hi.1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z i) vs DFrac.discard v Hi.1 $$ [Hs] as -
    · isplitl []
      · iexact Hs
      · ipureintro; exact Hv
    ihave ⟨%o, %Ho, #Hop⟩ := opsElems_lookup vs h (sint.nat i) v Hv $$ Hel
    iunfold opRep at Hop
    icases Hop with ⟨%Hf, #He⟩
    obtain ⟨hsnap, hhs, hidx, hterm⟩ := Hf
    ihave %Helen := ownSlice_len $$ He
    wp_join iprop(∃ bb1 : GoSlice, b_ptr ↦ bb1 ∗
        bb1 ↦* (bs ++ tU64 s.len ++ (h.take (sint.nat i)).flatMap tOpBytes ++
          tU64 (if o.snap then W64 1 else W64 0)) ∗ ownSliceCap w8 bb1 (DFrac.own 1))
      at next with [b Hb Hcap] as ⟨%bb1, b, Hb, Hcap⟩
    · rw [← hsnap]
      cases v.snap'
      · wp_auto
        wp_apply wp_putU64 $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
        wp_join_done
        iexists b2
        iframe
      · wp_auto
        wp_apply wp_putU64 $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
        wp_join_done
        iexists b2
        iframe
    wp_apply wp_putHS $$ [$Hb $Hcap] as %b3 ⟨Hb, Hcap⟩
    wp_apply wp_putU64 $$ [$Hb $Hcap] as %b4 ⟨Hb, Hcap⟩
    wp_apply wp_putU64 $$ [$Hb $Hcap] as %b5 ⟨Hb, Hcap⟩
    wp_apply wp_putU64 $$ [$Hb $Hcap] as %b6 ⟨Hb, Hcap⟩
    ihave HI2 : (∃ (j : w64) (bb : GoSlice),
        "j" ∷ j_ptr ↦ j ∗ "b" ∷ b_ptr ↦ bb ∗ "o" ∷ o_ptr ↦ v ∗
        "Hb" ∷ bb ↦* (bs ++ tU64 s.len ++ List.flatMap tOpBytes (List.take (sint.nat i) h) ++
          tU64 (if o.snap = true then W64 1 else W64 0) ++ tHsBytes v.hs' ++ tU64 v.idx' ++
          tU64 v.term' ++ tU64 v.ents'.len ++ (o.ents.take (sint.nat j)).flatMap tEntBytes) ∗
        "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z v.ents'.len⌝ : IProp GF) $$ [j b o Hb Hcap]
    · iexists W64 0, b6
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil,
        List.append_nil]
      iframe
      ipureintro; constructor <;> word
    wp_for HI2
    wp_if_destruct
    · have hjl : sint.nat j < o.ents.length := by
        have : sint.nat j < sint.nat v.ents'.len := by word
        omega
      obtain ⟨e, Hev⟩ : ∃ e, o.ents[sint.nat j]? = some e := ⟨_, List.getElem?_eq_getElem hjl⟩
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.ents'.len := ⟨Hj.1, Hif⟩
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index v.ents' (sint.Z j) o.ents DFrac.discard e Hj.1 $$ [He] as -
      · isplitl []
        · iexact He
        · ipureintro; exact Hev
      wp_apply wp_putU64 $$ [$Hb $Hcap] as %c1 ⟨Hb, Hcap⟩
      wp_apply wp_putU64 $$ [$Hb $Hcap] as %c2 ⟨Hb, Hcap⟩
      wp_apply wp_putU64 $$ [$Hb $Hcap] as %c3 ⟨Hb, Hcap⟩
      wp_apply wp_putU64 $$ [$Hb $Hcap] as %c4 ⟨Hb, Hcap⟩
      wp_for_post
      iframe
      iexists j + W64 1, c4
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [hj1, flatMap_take_succ o.ents tEntBytes _ e Hev]
      unfold tEntBytes
      simp only [List.append_assoc]
      iframe
      ipureintro; constructor <;> word
    · have hjn : sint.nat j = o.ents.length := by
        have : sint.nat j = sint.nat v.ents'.len := by word
        omega
      rw [flatMap_take_length o.ents tEntBytes _ hjn]
      wp_for_post
      iframe
      iexists i + W64 1, bb
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hi1, flatMap_take_succ h tOpBytes _ o Ho]
      unfold tOpBytes
      rw [w64_of_length o.ents v.ents'.len Helen, hhs, hidx, hterm]
      simp only [List.append_assoc]
      iframe
      ipureintro; constructor <;> word
  · have hin : sint.nat i = h.length := by
      have : sint.nat i = sint.nat s.len := by word
      omega
    rw [flatMap_take_length h tOpBytes _ hin]
    wp_end
    unfold tOpsBytes
    rw [w64_of_length h s.len (Hel_len ▸ Hlen)]
    simp only [List.append_assoc]
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
