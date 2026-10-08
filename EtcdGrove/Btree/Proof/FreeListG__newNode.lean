import EtcdGrove.Btree.Spec.FreeListG__newNode
import EtcdGrove.Btree.Lemmas.Alloc

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

theorem FreeListG.newNode.wp_proof : FreeListG.newNode.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ f
  wp_start as #Hfl
  wp_auto
  unfold isFreeList
  wp_apply sync.Mutex.wp_Lock $$ [$Hfl] as ⟨Hlocked, HR⟩
  unfold freeListInv
  icases HR with ⟨%sl, %ns, Hfield, Hsl, Hcap, Hns⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_if_destruct
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hfl $Hlocked Hfield Hsl Hcap Hns]
    · inext; iexists sl, ns; iframe
    wp_alloc n as Hn
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hn
    iStructNamed Hn
    wp_auto
    iapply HΦ
    unfold freeNode nodeFields
    iexists _, _, _
    iframe
    rw [show (zero_val (node V)).items' = slice.nil from rfl,
      show (zero_val (node V)).children' = slice.nil from rfl]
    ihave H1 := ownSlice_nil (V := V) (GF := GF) (DFrac.own 1)
    ihave H2 := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave H3 := ownSliceCap_nil (V := V) (GF := GF)
    ihave H4 := ownSliceCap_nil (V := Loc) (GF := GF)
    isplitr
    · ipureintro; exact Hnn
    isplitr; · iexact H1
    isplitr; · iexact H3
    isplitr; · iexact H2
    iexact H4
  · have hi : sint.nat (sl.len - W64 1) + 1 = ns.length := by word
    list_elem ns (sint.nat (sl.len - W64 1)) as n
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) ns _ n (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hn_lookup
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_store_slice_index sl (sint.Z (sl.len - W64 1)) _ null $$ [Hsl] as Hsl
    · iframe; ipureintro; constructor <;> word
    wp_auto
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
    wp_auto
    icases ownSlice_slice_with_cap (W64 0) (sl.len - W64 1) sl _ ⟨by word, by word, by word⟩
      $$ [Hsl Hcap] with ⟨-, Hsl, Hcap⟩
    · iframe
    icases bigSepL_pop _ ns _ n Hn_lookup hi $$ Hns with ⟨Hns, Hn⟩
    have hsub : subslice (sint.nat (W64 0)) (sint.nat (sl.len - W64 1))
        (ns.set (sint.Z (sl.len - W64 1)).toNat null) = ns.take (sint.nat (sl.len - W64 1)) := by
      simp only [subslice, List.drop_zero, show sint.nat (W64 0) = 0 from rfl]
      rw [show (sint.Z (sl.len - W64 1)).toNat = sint.nat (sl.len - W64 1) from rfl,
        List.take_set_of_le (by omega)]
    rw [hsub]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hfl $Hlocked Hfield Hsl Hcap Hns]
    · inext; iexists _, _; iframe
    iapply HΦ $$ Hn

end proof

end Btree
end EtcdGrove
end Perennial
