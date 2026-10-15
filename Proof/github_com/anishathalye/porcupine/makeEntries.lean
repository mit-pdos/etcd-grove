/- Lean-first (no Rocq counterpart). Proof of `Spec/github_com/anishathalye/porcupine/makeEntries.lean`.

The range loop appends each operation's call and return entries (after `n` iterations,
`entries` is `rawEntries (ops.take n)`); `sort.Sort(byTime(entries))` (a sorter over the slice,
by the strict weak order `entryLt`) permutes them into a sorted order, and
`entriesFor_of_sorted` concludes.
-/
module

public import Spec.github_com.anishathalye.porcupine.makeEntries
public import Spec.github_com.anishathalye.porcupine.byTime__Len
public import Spec.github_com.anishathalye.porcupine.byTime__Less
public import Spec.github_com.anishathalye.porcupine.byTime__Swap
public import Spec.sort.Sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

omit package_sem in
/-- `byTime` over the slice `sl` sorts the entries it holds by `entryLt`. -/
theorem byTime_sorter
    (hLen : byTime.Len.spec (GF := GF) (hG := hG))
    (hLess : byTime.Less.spec (GF := GF) (hG := hG))
    (hSwap : byTime.Swap.spec (GF := GF) (hG := hG)) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ⊢
      sorterSpec (interface.mk github_com.anishathalye.porcupine.byTime.ty #sl)
        (fun es => iprop(sl ↦* es)) entryLt := by
  iintro #Hpkg
  unfold sorterSpec
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ Hs HΦ
    wp_apply (hLen sl l (DFrac.own 1)) $$ [$Hs] as Hs
    iapply HΦ $$ Hs
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ Hs HΦ
    wp_apply (hLess sl l (DFrac.own 1) i j a b) $$ [$Hs] as Hs
    · ipureintro; exact Hij
    iapply HΦ $$ Hs
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ Hs HΦ
  wp_apply (hSwap sl l i j a b) $$ [$Hs] as Hs
  · ipureintro; exact Hij
  iapply HΦ $$ Hs

theorem makeEntries.wp_proof
    (hSort : sort.«Sort».spec (GF := GF) (hG := hG))
    (hLen : byTime.Len.spec (GF := GF) (hG := hG))
    (hLess : byTime.Less.spec (GF := GF) (hG := hG))
    (hSwap : byTime.Swap.spec (GF := GF) (hG := hG)) :
    makeEntries.spec (GF := GF) (hG := hG) :=
  fun sl ops dq hok => by
  wp_start as Hs
  wp_auto
  have hn := hok.1
  ihave Hnil : (slice.nil ↦* ([] : List entry)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap entry slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave %Hslen := ownSlice_len $$ Hs
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : Operation),
      "i" ∷ i_ptr ↦ n ∗
      "entries" ∷ entries_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ n ∗
      "elem" ∷ elem_ptr ↦ x ∗
      "He" ∷ s' ↦* rawEntries (ops.take (sint.nat n)) ∗
      "Hcap" ∷ ownSliceCap entry s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ops.length : Int)⌝) $$ [i entries id elem Hnil Hcap]
  · iexists W64 0, slice.nil, zero_val Operation
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, rawEntries_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ops.length := by word
    obtain ⟨o, Ho⟩ : ∃ o, ops[sint.nat n]? = some o := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index sl (sint.Z n) _ _ o Hn.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Ho
    have hW : W64 ((sint.nat n : Nat) : Int) = n := by word
    have hcall : (⟨false, o.Input', n, o.Call', o.ClientId', o.Metadata'⟩ : entry) =
        callE o (sint.nat n) := by simp only [callE, hW]
    have hret : (⟨true, o.Output', n, o.Return', o.ClientId', o.Metadata'⟩ : entry) =
        retE o (sint.nat n) := by simp only [retE, hW]
    rw [hcall]
    wp_apply wp_slice_literal (V := entry) [callE o (sint.nat n)]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$He $Hcap $Hsl2] as %s3 ⟨He, Hcap, -⟩
    rw [hret]
    wp_apply wp_slice_literal (V := entry) [retE o (sint.nat n)]
    isplitr
    · ipureintro; rfl
    iintro %sl4 ⟨Hsl4, -⟩
    wp_apply wp_slice_append $$ [$He $Hcap $Hsl4] as %s5 ⟨He, Hcap, -⟩
    wp_for_post
    have Htake : ops.take (sint.nat (n + W64 1)) = ops.take (sint.nat n) ++ [o] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Ho]; rfl
    have Htl : (ops.take (sint.nat n)).length = sint.nat n := by
      rw [List.length_take]; omega
    iframe HΦ Hs
    iexists n + W64 1, s5, o
    simp only [named, Htake, rawEntries_snoc, Htl, List.append_assoc, List.cons_append,
      List.nil_append]
    iframe
    ipureintro; constructor <;> word
  · have Hn' : sint.nat n = ops.length := by word
    rw [Hn', List.take_length]
    ihave #Hpsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
    · iPkgInit
    ihave #Hsorter := byTime_sorter hLen hLess hSwap s' $$ Hpkg
    wp_apply (hSort entry _ (fun es => iprop(s' ↦* es)) entryLt (rawEntries ops) entryLt_swo)
      $$ [He] as %l' ⟨He, %Hl'⟩
    · iframe #
      iframe He
      ipureintro
      rw [rawEntries_length]
      omega
    iapply HΦ
    iexists l'
    iframe He Hs
    ipureintro
    exact entriesFor_of_sorted hok Hl'.1 Hl'.2

end proof

end porcupine
end EtcdGrove
end Perennial
