/-
Lean-first (no Rocq counterpart).

The proof of `(*histHashes).intern`: the maps made if `canon` is nil; then `canon[k]`'s nodes (taken
out of the map, or none), each compared with `st` (`storeEqual`): an equal one holds the history, by
its `canonNode` facts; otherwise a new node, appended to `canon[k]` and recorded in `is`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__intern
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeHash
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A literal of one unkeyed element has one element. -/
theorem arrayLiteralSize1 {a} : go.arrayLiteralSize [KeyedElement none a] = 1 := rfl

theorem histHashes.intern.wp_proof (wp_storeHash : storeHash.spec (GF := GF) (hG := hG))
    (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG)) :
    histHashes.intern.spec (GF := GF) (hG := hG) := by
  intro hh prev hs st s n
  wp_start as ⟨Hinv, #Hprev, #Hst, %Hn⟩
  iunfold hhInv at Hinv
  icases Hinv with ⟨%mc, %mi, %mg, %C, %I, %G, Hc, Hi, Hg, Hci, Hgs⟩
  (try wp_auto)
  wp_join iprop(∃ (mc' mi' : GoMap) (C' : GMap ikey GoSlice) (I' : GMap Loc Bool),
      hh_ptr ↦ hh ∗ structFieldRef histHashes go!"canon" hh ↦ mc' ∗ structFieldRef histHashes go!"is" hh ↦ mi' ∗
      mc' ↦$ C' ∗ mi' ↦$ I' ∗
      [∗map] k ↦ sl ∈ C', ∃ ns : List Loc, sl ↦* ns ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
        [∗list] n ∈ ns, canonNode k n) with [hh Hc Hi Hci]
      as ⟨%mc', %mi', %C', %I', hh, Hc, Hi, HC, HI, HCs⟩
  · (try wp_auto)
    wp_apply (wp_map_make1 (K := ikey) (V := GoSlice) _ _) as %m1 Hm1
    (try wp_auto)
    wp_apply (wp_map_make1 (K := Loc) (V := Bool) _ _) as %m2 Hm2
    (try wp_auto)
    iexists m1, m2, ∅, ∅
    iframe
    iapply BigSepM.bigSepM_empty.2
    itrivial
  · icases Hci with (%Hnil | ⟨HC, HI, HCs⟩)
    · exact absurd Hnil.1 (by assumption)
    · iexists mc, mi, C, I
      iframe
  wp_apply wp_storeHash st s $$ [Hst] as %hv -
  (try wp_auto)
  wp_apply (wp_map_lookup1 _ _ mc' C' (ikey.mk prev n hv) (DFrac.own 1)) $$ [HC] as HC
  ihave Hsl : (∃ ns : List Loc,
      ((C' !! ikey.mk prev n hv).getD (zero_val GoSlice)) ↦* ns ∗
      ownSliceCap Loc ((C' !! ikey.mk prev n hv).getD (zero_val GoSlice)) (DFrac.own 1) ∗
      ([∗list] c ∈ ns, canonNode (ikey.mk prev n hv) c) ∗
      ⌜ns = [] ∨ C' !! ikey.mk prev n hv = some ((C' !! ikey.mk prev n hv).getD (zero_val GoSlice))⌝ ∗
      (∀ sl' : GoSlice, (∃ ns' : List Loc, sl' ↦* ns' ∗ ownSliceCap Loc sl' (DFrac.own 1) ∗
          [∗list] c ∈ ns', canonNode (ikey.mk prev n hv) c) -∗
        [∗map] k ↦ sl ∈ <[ikey.mk prev n hv := sl']> C', ∃ ns : List Loc, sl ↦* ns ∗
          ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] n ∈ ns, canonNode k n) : IProp GF) $$ [HCs]
  · cases hC : C' !! ikey.mk prev n hv with
    | none =>
      ihave Hrest := (BigSepM.bigSepM_subseteq (m₂ := Iris.Std.PartialMap.delete C' (ikey.mk prev n hv))
        LawfulPartialMap.delete_subset_self) $$ HCs
      iexists []
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplitr
      · ipureintro; exact .inl rfl
      iintro %sl' Hsl'
      iapply BigSepM.bigSepM_insert_delete.2
      iframe
    | some sl0 =>
      icases (BigSepM.bigSepM_delete hC).1 $$ HCs with ⟨⟨%ns, Hns, Hcap, #Hcn⟩, Hrest⟩
      iexists ns
      iframe
      isplitr
      · ipureintro; exact .inr rfl
      iintro %sl' Hsl'
      iapply BigSepM.bigSepM_insert_delete.2
      iframe
  icases Hsl with ⟨%ns, Hns, Hcap, #Hcn, %Hns0, Hback⟩
  ihave %Hlns := ownSlice_len $$ Hns
  (try wp_auto)
  fail "ctx2"

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
