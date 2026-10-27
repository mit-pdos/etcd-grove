/-
Proof of `Spec/k8s_io/client_go/tools/cache/cache__Transaction.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.cache__Transaction
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Transaction

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem cache.Transaction.wp_proof
    (wp_Txn : threadSafeMap.Transaction.spec (GF := GF) (hG := hG)) :
    cache.Transaction.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf D KF rvOf sl dq xs hty
  obtain ⟨hts, -, -⟩ := hty
  iintro %Φ ⟨#Hpkg, #Hca, #Hkey, #Hacc, Hsl, %Htys, #Hoks⟩ HAU
  iunfold isCache at Hca
  icases Hca with ⟨#Hcs, #Hkf, #Htr, #Hts⟩
  iunfold keyOk at Hkey
  wp_method_call
  wp_call
  wp_auto
  simp only [hts, ↓reduceIte]
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_apply (wp_slice_make3 (V := ThreadSafeStoreTransaction) (W64 0) sl.len (by word))
    as %ks0 ⟨Hks0, Hkcap0, -⟩
  (try wp_auto)
  wp_apply (wp_slice_make3 (V := w64) (W64 0) sl.len (by word)) as %si0 ⟨Hsi0, Hscap0, -⟩
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GoInterface) (W64 0)) as %es0 ⟨Hes0, Hecap0⟩
  · ipureintro; word
  (try wp_auto)
  rename_i iu_ptr
  irename i => iu
  ihave IH : iprop(∃ (n : w64) (ks si : GoSlice) (is : List w64) (iv : w64),
      "i" ∷ i_ptr ↦ n ∗ "iu" ∷ iu_ptr ↦ iv ∗
      "kt" ∷ keyedTxns_ptr ↦ ks ∗ "Hks" ∷ ks ↦* ((xs.take (sint.nat n)).map (fun x => (x.keyed KF).go)) ∗
      "Hkcap" ∷ ownSliceCap ThreadSafeStoreTransaction ks (DFrac.own 1) ∗
      "sx" ∷ successfulIndices_ptr ↦ si ∗ "Hsi" ∷ si ↦* is ∗
      "Hscap" ∷ ownSliceCap w64 si (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i iu keyedTxns Hks0 Hkcap0 successfulIndices Hsi0 Hscap0]
  · iexists W64 0, ks0, si0, _, _
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by
      have := Hlen.1; simp only [List.length_map] at this; word
    obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hidx : (xs.map Tx.txn)[(sint.Z n).toNat]? = some x.txn := by
      rw [show (sint.Z n).toNat = sint.nat n by word, List.getElem?_map, Hx]; rfl
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) (xs.map Tx.txn) dq x.txn Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hidx
    (try wp_auto)
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) (xs.map Tx.txn) dq x.txn Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hidx
    ihave #Hx := BigSepL.bigSepL_lookup (Φ := fun _ (x : Tx) => iprop(D x.o ∗ OK x.o)) Hx $$ Hoks
    icases Hx with ⟨#HDx, #HOKx⟩
    (try wp_auto)
    wp_apply Hkey $$ [$HDx]
    iintro %k %err %hk
    obtain ⟨rfl, rfl⟩ := hk
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hsi $Hscap $Hl1] as %si' ⟨Hsi, Hscap, -⟩
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l2 ⟨Hl2, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hks $Hkcap $Hl2] as %ks' ⟨Hks, Hkcap, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, ks', si', _, _
    iframe
    isplitl
    · have : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [this, List.take_add_one, Hx]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
      rw [show (Tx.keyed KF x).go = ⟨x.txn, KF x.o⟩ from rfl]
      iexact Hks
    · ipureintro; word
  · have hn : sint.nat n = xs.length := by
      have := Hlen.1; simp only [List.length_map] at this; word
    rw [hn, List.take_length] at *
    (try wp_auto)
    wp_bind
    iapply (wp_Txn ts γ OK Fam D rvOf ks (DFrac.own 1) (xs.map (Tx.keyed KF)))
      $$ [$Hpkg $Hts $Hacc Hks]
    · rw [List.map_map]
      isplitl [Hks]
      · rw [show (Tx.go ∘ Tx.keyed KF) = (fun x => (Tx.keyed KF x).go) from rfl]
        iexact Hks
      isplitr
      · ipureintro
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        exact Htys x hx
      rw [BigSepL.bigSepL_map]
      simp only [Tx.keyed_o]
      imodintro
      iexact Hoks
    inext
    imod HAU with ⟨%σ, Hst, Hcl⟩
    imodintro
    iexists σ
    iframe Hst
    iintro Hst
    imod Hcl $$ Hst with HK
    imodintro
    iintro -
    (try wp_auto)
    ihave %Hel := ownSlice_len _ _ _ $$ Hes0
    rw [show sint.Z es0.len = 0 by have := Hel.1; simp at this; word]
    (try wp_auto)
    iapply HK; iexact Hsl

end proof

end cache
end EtcdGrove
end Perennial
