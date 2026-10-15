/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/bucketBuffer__merge.lean`.
Lean-first (no Rocq counterpart).

The loop adds `src`'s entries one by one (`add`); then the buffer is `es ++ es2`. If `bb` was
empty, that is `es2`, canonical already. Otherwise the last of `es` is compared with the key of
`src`'s first slot (stale when `src` is empty: `slotsRO` gives it some bytes): below it, the
concatenation is sorted, so canonical; else `dedupe` makes it canonical.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__merge
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__add
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__dedupe
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ModelLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.MergeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.bucketBuffer.merge.wp_proof
    (hAdd : backend.bucketBuffer.add.spec (GF := GF) (hG := hG))
    (hDedupe : backend.bucketBuffer.dedupe.spec (GF := GF) (hG := hG)) :
    backend.bucketBuffer.merge.spec (GF := GF) (hG := hG) := by
  intro bb es src es2 Hs Hs2 Hbound
  wp_start as ⟨Hbb, Hsrc⟩
  iunfold ownBB at Hsrc
  icases Hsrc with ⟨%p2, Hsrc, %Hok2⟩
  iunfold bbAt at Hsrc
  icases Hsrc with ⟨Hsrc, Hbuf2, Hcap2, #Hro2, #Hents2⟩
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hbuf2
  wp_auto
  have hb2 : es2.length < p2.kvs.length := Hok2.1
  ihave HI : (∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "Hbb" ∷ ownBB bb (es ++ es2.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ es2.length⌝ : IProp GF) $$ [i Hbb]
  · iexists (W64 0)
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, List.take_zero, List.append_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hilt : sint.nat i < es2.length := by word
    have hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p2.buf.len := by word
    simp only [hbi, _root_.and_self, ite_true]
    list_elem es2 (sint.nat i) as e
    list_elem p2.kvs (sint.nat i) as x
    ihave #Hx := entsIn_slot p2.kvs es2 (sint.nat i) x e Hx_lookup He_lookup $$ Hents2
    icases Hx with ⟨#Hxk, #Hxv⟩
    icases ownSlice_elem_acc (sint.Z i) x p2.buf _ p2.kvs (by word) Hx_lookup $$ Hbuf2
      with ⟨Hel, Hback⟩
    wp_auto
    simp only [hbi, _root_.and_self, ite_true]
    wp_auto
    ihave Hbuf2 := Hback $$ %x Hel
    rw [list_set_lookup_self p2.kvs (sint.Z i).toNat x Hx_lookup]
    wp_apply (hAdd bb (es ++ es2.take (sint.nat i)) x.key' x.val' e.1 e.2
      (by simp only [List.length_append, List.length_take]; unfold bufBound at Hbound ⊢; omega))
      $$ [$Hbb $Hxk $Hxv] as Hbb
    wp_for_post
    iframe
    iexists (i + W64 1)
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [hi1, List.take_add_one, He_lookup, Option.toList_some, List.append_assoc]
    iframe
    ipureintro; word
  · have hie : sint.nat i = es2.length := by word
    rw [hie, List.take_length]
    iunfold ownBB at Hbb
    icases Hbb with ⟨%p, Hbb, %Hok⟩
    iunfold bbAt at Hbb
    icases Hbb with ⟨Hbb, Hbuf, Hcap, #Hro, #Hents⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hbuf
    have hlen : (es ++ es2).length = es.length + es2.length := List.length_append
    have hB : es.length + es2.length < 2 ^ 60 := Hbound
    wp_auto
    wp_if_destruct
    · -- `bb` was empty
      have hes : es.length = 0 := by
        rw [hlen] at Hif
        clear hlen Hok Hl Hok2 Hl2 hb2 Hi hie
        word
      have hes' : es = [] := List.eq_nil_of_length_eq_zero hes
      subst hes'
      simp only [List.nil_append] at Hok ⊢
      rw [canon_of_sorted Hs2]
      iapply HΦ
      isplitl [Hbb Hbuf Hcap]
      · iunfold ownBB; iexists p; iunfold bbAt; iframe; iframe Hro Hents; ipureintro; exact Hok
      · iunfold ownBB; iexists p2; iunfold bbAt; iframe; iframe Hro2 Hents2; ipureintro; exact Hok2
    · have hne : es.length ≠ 0 := by
        intro h; apply Hif; rw [hlen, h, Nat.zero_add]
      obtain ⟨j, hj⟩ : ∃ j : w64,
          j = W64 ↑(es ++ es2).length - W64 ↑es2.length - W64 1 := ⟨_, rfl⟩
      rw [← hj]
      have hjZ : sint.Z j = ((es.length - 1 : Nat) : Int) := by
        rw [hj, hlen]
        clear hj hlen Hok Hl Hok2 Hl2 hb2 Hi hie Hif
        word
      have hjn : sint.nat j = es.length - 1 := by
        show (sint.Z j).toNat = _; rw [hjZ]; omega
      have hpk : (es ++ es2).length < p.kvs.length := Hok.1
      have hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z p.buf.len := by
        rw [hlen] at hpk
        have h1 := Hl.1
        clear hj hlen Hok Hok2 Hl2 hb2 Hi hie Hif
        constructor <;> word
      simp only [hbj, _root_.and_self, ite_true]
      list_elem es (es.length - 1) as a
      list_elem p.kvs (sint.nat j) as x
      have ha' : (es ++ es2)[sint.nat j]? = some a := by
        rw [List.getElem?_append_left (by omega), hjn]; exact Ha_lookup
      ihave #Hx := entsIn_slot p.kvs (es ++ es2) (sint.nat j) x a Hx_lookup ha' $$ Hents
      icases Hx with ⟨#Hxk, -⟩
      list_elem p2.kvs 0 as x0
      ihave #Hk0 : (∃ k0 : GoString, x0.key' ↦*□ k0 ∗ ⌜∀ e, es2[0]? = some e → k0 = e.1⌝) $$ []
      · cases h : es2[0]? with
        | some e =>
          iexists e.1
          ihave #H := entsIn_slot p2.kvs es2 0 x0 e Hx0_lookup h $$ Hents2
          icases H with ⟨#Hk, -⟩
          iframe Hk
          ipureintro
          intro e' he'; cases he'; rfl
        | none =>
          ihave #H := slotsRO_slot p2.kvs 0 x0 Hx0_lookup $$ Hro2
          icases H with ⟨%b1, %b2, #Hk, -⟩
          iexists b1
          iframe Hk
          ipureintro
          intro e' he'; cases he'
      icases Hk0 with ⟨%k0, #Hk0, %Hk0e⟩
      icases ownSlice_elem_acc (sint.Z j) x p.buf _ p.kvs hbj.1 Hx_lookup $$ Hbuf
        with ⟨Hel, Hback⟩
      wp_auto
      ihave Hbuf := Hback $$ %x Hel
      rw [list_set_lookup_self p.kvs (sint.Z j).toNat x Hx_lookup]
      have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z p2.buf.len := by
        have h1 := Hl2.1
        clear hj hlen Hok Hok2 Hl Hi hie Hif hjZ hjn hbj Ha_lookup Hx_lookup ha' Hx0_lookup
        constructor <;> word
      simp only [hb0, _root_.and_self, ite_true]
      icases ownSlice_elem_acc (sint.Z (W64 0)) x0 p2.buf _ p2.kvs hb0.1 Hx0_lookup $$ Hbuf2
        with ⟨Hel, Hback⟩
      wp_auto
      ihave Hbuf2 := Hback $$ %x0 Hel
      rw [list_set_lookup_self p2.kvs (sint.Z (W64 0)).toNat x0 Hx0_lookup]
      wp_apply bytes.wp_Compare x.key' x0.key' DFrac.discard DFrac.discard a.1 k0
        $$ [$Hxk $Hk0] as ⟨-, -⟩
      rw [compare_neg]
      wp_if_destruct
      · -- sorted already
        have hsorted : entsSorted (es ++ es2) := by
          cases h : es2[0]? with
          | none =>
            have : es2 = [] := by
              cases es2 with
              | nil => rfl
              | cons _ _ => cases h
            subst this
            rw [List.append_nil]; exact Hs
          | some b =>
            have hk := Hk0e b h
            subst hk
            exact entsSorted_append_of_last_lt Hs Hs2 a b Ha_lookup h Hif
        rw [canon_of_sorted hsorted]
        iapply HΦ
        isplitl [Hbb Hbuf Hcap]
        · iunfold ownBB; iexists p; iunfold bbAt; iframe; iframe Hro Hents; ipureintro; exact Hok
        · iunfold ownBB; iexists p2; iunfold bbAt; iframe; iframe Hro2 Hents2; ipureintro; exact Hok2
      · wp_apply (hDedupe bb (es ++ es2)) $$ [Hbb Hbuf Hcap] as Hbb
        · iunfold ownBB; iexists p; iunfold bbAt; iframe; iframe Hro Hents; ipureintro; exact Hok
        iapply HΦ
        iframe Hbb
        iunfold ownBB; iexists p2; iunfold bbAt; iframe; iframe Hro2 Hents2; ipureintro; exact Hok2

end proof

end EtcdGrove
end Perennial
