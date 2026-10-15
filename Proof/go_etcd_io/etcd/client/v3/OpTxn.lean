/-
Proof of `Spec/go_etcd_io/etcd/client/v3/OpTxn.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.OpTxn
public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

private theorem set_replicate {A : Type} (cvs : List A) (z c : A) (k : Nat) (hk : 0 < k) :
    (cvs ++ List.replicate k z).set cvs.length c = (cvs ++ [c]) ++ List.replicate (k - 1) z := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [List.replicate_succ]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem OpTxn.wp_proof (wp_Clone : Cmp.Clone.spec (GF := GF) (hG := hG)) :
    OpTxn.spec (GF := GF) (hG := hG) := by
  intro csl ms tsl esl
  wp_start as #Hcs
  iapply wp_fupd
  ihave #Hcs' := Hcs
  unfold cmpsAt
  icases Hcs' with ⟨%cs, #Hsl, %Hlen, #Hall⟩
  ihave %Hslen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply wp_slice_make2 (V := go_etcd_io.etcd.client.v3.Cmp) csl.len as %sl0 ⟨Hs0, -⟩
  · ipureintro; exact Hslen.2
  ihave %Hl0 := ownSlice_len _ _ _ $$ Hs0
  simp only [List.length_replicate] at Hl0
  (try wp_auto)
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Hgi
  ihave IH : iprop(∃ (n k : w64) (cvs : List go_etcd_io.etcd.client.v3.Cmp),
      "i" ∷ i_ptr ↦ n ∗ "Hgi" ∷ igo ↦ k ∗
      "Hs0" ∷ sl0 ↦* (cvs ++ List.replicate (sint.nat csl.len - sint.nat n) (zero_val go_etcd_io.etcd.client.v3.Cmp)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z csl.len ∧ cvs.length = sint.nat n⌝ ∗
      "#Hcv" ∷ □ (∀ (j : Nat) (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel), ⌜cvs[j]? = some c⌝ -∗
        ⌜ms[j]? = some m⌝ -∗ cmpAt c m)) $$ [i Hgi Hs0]
  · iexists W64 0, _, []
    simp only [named]
    iframe
    rw [show sint.nat (W64 0) = 0 by rfl]
    try simp only [List.nil_append, Nat.sub_zero]
    iframe
    isplitr
    · ipureintro; refine ⟨by word, by word, rfl⟩
    imodintro
    iintro %j %c %m %h
    simp at h
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < cs.length := by word
    obtain ⟨c, Hci⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨m, Hmi⟩ : ∃ m, ms[sint.nat n]? = some m := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z csl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index csl (sint.Z n) cs DFrac.discard c Hn.1 $$ [$Hsl] as -
    · ipureintro; exact Hci
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    ihave #Hcm := Hall $$ %(sint.nat n) %c %m %Hci %Hmi
    icases ownSlice_elem_acc (sint.Z n) c csl DFrac.discard cs Hn.1 Hci $$ Hsl with ⟨Hel, -⟩
    wp_apply wp_Clone $$ [$Hpkg $Hel $Hcm] as %c' ⟨-, %Hnn, Hown⟩
    unfold compareOwn
    icases Hown with ⟨%ksl, %esl', %u, Hres, #Htgt, #Hkey, #Hks, Hend, #Hes, Hu, #Hua⟩
    ipersist Hres
    ipersist Hend
    ipersist Hu
    ihave #Hc' : cmpAt (GF := GF) c' m $$ []
    · unfold cmpAt compareAt
      isplitl []
      · ipureintro; exact Hnn
      iexists ksl, esl', u
      iframe #
    (try wp_auto)
    rw [ite_eq_left (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl0.len from ⟨Hn.1, by word⟩)]
    wp_apply wp_store_slice_index $$ [$Hs0] as Hs0
    · ipureintro
      constructor
      · exact Hn.1
      · simp only [List.length_append, List.length_replicate]; word
    have hk : 0 < sint.nat csl.len - sint.nat n := by word
    rw [show (sint.Z n).toNat = cvs.length by word, set_replicate cvs _ c' _ hk] at *
    wp_for_post
    iframe
    iexists n + W64 1, n, cvs ++ [c']
    simp only [named]
    iframe
    rw [show sint.nat csl.len - sint.nat (n + W64 1) = sint.nat csl.len - sint.nat n - 1 by word]
    iframe
    isplitr
    · ipureintro; refine ⟨by word, by word, by simp; word⟩
    imodintro
    iintro %j %c0 %m0 %Hj %Hm0
    rcases Nat.lt_or_ge j cvs.length with hj | hj
    · rw [List.getElem?_append_left hj] at Hj
      iapply Hcv $$ %j %c0 %m0 %Hj %Hm0
    · rw [List.getElem?_append_right hj] at Hj
      have : j - cvs.length = 0 := by
        rcases h : j - cvs.length with _ | _
        · rfl
        · rw [h] at Hj; simp at Hj
      rw [this] at Hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hj
      subst Hj
      have : j = sint.nat n := by omega
      subst this
      rw [Hmi] at Hm0
      cases Hm0
      iexact Hc'
  · have Hfull : sint.nat n = sint.nat csl.len := by word
    rw [Hfull, Nat.sub_self, List.replicate_zero, List.append_nil]
    ipersist Hs0
    imodintro
    iapply HΦ
    isplitl []
    · unfold opFullAt opAt OpFields opSortAt
      simp only [OpFull.txnInit, OpFull.newOp, OpModel.zero]
      ihave #Hnil := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
      iframe #
      simp
      isplitl []
      · itrivial
      isplitl []
      · itrivial
      itrivial
    isplitl []
    · iexists cvs
      iframe #
      ipureintro; omega
    ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
