/- Lean-first (no Rocq counterpart).

Proof of `writerCodec.spec` (#50 N10a).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerCodec
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterCodecDefs
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__I64
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.NewDec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__I64
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Done

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client
open etcd_dist etcdstart
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

theorem writerCodec.wp_proof
    (wp_EncInt : Enc.Int.spec (GF := GF) (hG := hG))
    (wp_EncStr : Enc.Str.spec (GF := GF) (hG := hG))
    (wp_EncI64 : Enc.I64.spec (GF := GF) (hG := hG))
    (wp_NewDec : NewDec.spec (GF := GF) (hG := hG))
    (wp_DecInt : Dec.Int.spec (GF := GF) (hG := hG))
    (wp_DecStr : Dec.Str.spec (GF := GF) (hG := hG))
    (wp_DecI64 : Dec.I64.spec (GF := GF) (hG := hG))
    (wp_Done : Dec.Done.spec (GF := GF) (hG := hG)) :
    writerCodec.spec (GF := GF) (hG := hG) := by
  intro N P Q
  wp_start
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold wireOk
  simp only [writerWire]
  isplitr
  · -- EncIn
    iintro %x %i !> %Φ' ⟨%sl, ⟨%Hx, %Hlen⟩, #Hsl⟩ HΦ'
    subst Hx
    ihave %Hsl_len := ownSlice_len _ _ _ $$ Hsl
    wp_auto
    ihave He : ownEnc «$r0_ptr» [] $$ [«$r0»]
    · unfold ownEnc
      iexists slice.nil
      iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    wp_apply wp_EncInt _ _ sl.len $$ [He] as He
    · iframe
    (try wp_auto)
    isimp only [List.nil_append] at He
    ihave IH : (∃ (j : Nat) (pv : wkv),
        "i" ∷ i_ptr ↦ W64 j ∗ "p" ∷ p_ptr ↦ pv ∗
        "He" ∷ ownEnc «$r0_ptr» (encU64 sl.len ++ kvsBody (i.2.take j)) ∗
        "%Hj" ∷ ⌜j ≤ i.2.length⌝ : IProp GF) $$ [i p He]
    · iexists 0, _
      rw [List.take_zero, kvsBody_nil, List.append_nil]
      iframe
      ipureintro; omega
    wp_for IH
    by_cases hj : j < i.2.length
    · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
      simp only [decide_eq_true hc, ↓reduceIte]
      (try wp_auto)
      have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      simp only [h0, hc, _root_.and_self, ↓reduceIte]
      have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
      obtain ⟨x, hx⟩ : ∃ x, i.2[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
      wp_apply (wp_load_slice_index sl (sint.Z (W64 (j : Int))) i.2 DFrac.discard x h0) $$ [] as -
      · iframe #; ipureintro; rw [hsj]; exact hx
      (try wp_auto)
      wp_apply wp_EncStr _ _ x.Key' $$ [He] as He
      · iframe
      (try wp_auto)
      wp_apply wp_EncStr _ _ x.Val' $$ [He] as He
      · iframe
      (try wp_auto)
      wp_for_post
      iframe
      iexists (j + 1), x
      have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
      have hb : encU64 sl.len ++ kvsBody (i.2.take (j + 1)) =
          encU64 sl.len ++ kvsBody (i.2.take j) ++ encStr x.Key' ++ encStr x.Val' := by
        rw [kvsBody_take_succ _ _ _ hx]; simp only [List.append_assoc]
      rw [hw, hb]
      iframe
      ipureintro; omega
    · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
      simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
      have hjl : j = i.2.length := by omega
      subst hjl
      rw [List.take_length]
      (try wp_auto)
      iunfold ownEnc at He
      icases He with ⟨%s, He, Hs, -⟩
      (try wp_auto)
      iapply HΦ'
      have e : capped (kvsBytes i.2) = encU64 sl.len ++ kvsBody i.2 := by
        rw [capped_of _ Hlen, kvsBytes_eq]
        obtain ⟨h1, h2⟩ := Hsl_len
        congr 2
        word
      rw [e]
      iexact Hs
  isplitr
  · -- DecIn
    iintro %i %b %dq !> %Φ' Hb HΦ'
    wp_auto
    wp_apply wp_NewDec b _ dq $$ [Hb] as %d Hd
    · iframe
    (try wp_auto)
    wp_apply wp_DecInt d _ true $$ [Hd] as %n Hd
    · iframe
    icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r1, %ok1, Hd, %H1⟩
    (try wp_auto)
    ihave IH : (∃ (j : w64) (ps : List wkv) (s : GoSlice) (r : List w8) (ok : Bool) (s0 : GoSlice)
        (dq0 : DFrac),
        "i" ∷ i_ptr ↦ j ∗ "ps" ∷ ps_ptr ↦ s ∗ "Hs" ∷ s ↦* ps ∗
        "Hcap" ∷ ownSliceCap wkv s (DFrac.own 1) ∗
        "Hd" ∷ d ↦ ({ B' := s0, Ok' := ok } : Dec) ∗ "Hs0" ∷ s0 ↦*{dq0} r ∗
        "%Hok" ∷ ⌜ok = true → capped (kvsBytes i.2) = encU64 n ++ kvsBody ps ++ r⌝ : IProp GF)
        $$ [i ps Hd]
    · iunfold ownDec at Hd
      icases Hd with ⟨%s0, %dq0, Hd, Hs0⟩
      iexists W64 0, [], slice.nil, r1, ok1, s0, dq0
      iframe
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      ipureintro
      intro h
      obtain ⟨-, h⟩ := H1 h
      rw [h, kvsBody_nil, List.append_nil]
    wp_for IH
    cases ok
    · -- the flag is false: the loop ends
      (try wp_auto)
      try simp only [val_false_ne_true, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      try simp only [decide_eq_true_eq, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      ihave Hdd : ownDec d r false $$ [Hd Hs0]
      · unfold ownDec; iexists s0, dq0; iframe
      wp_apply wp_Done d r false $$ [Hdd] as %dn %Hdn
      · iframe
      (try wp_auto)
      iapply HΦ'
      iintro %hdn
      exact absurd (Hdn hdn).1 Bool.false_ne_true
    · by_cases hc : sint.Z j < sint.Z n
      · (try wp_auto)
        simp only [decide_eq_true hc]
        simp only [_root_.decide_true, ↓reduceIte]
        (try wp_auto)
        ihave Hdd : ownDec d r true $$ [Hd Hs0]
        · unfold ownDec; iexists s0, dq0; iframe
        wp_apply wp_DecStr d r true $$ [Hdd] as %k Hdd
        · iframe
        icases decPost_elim _ _ _ _ _ $$ Hdd with ⟨%r2, %ok2, Hdd, %H2⟩
        (try wp_auto)
        wp_apply wp_DecStr d r2 ok2 $$ [Hdd] as %v Hdd
        · iframe
        icases decPost_elim _ _ _ _ _ $$ Hdd with ⟨%r3, %ok3, Hdd, %H3⟩
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl', -⟩
        wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl'] as %s1 ⟨Hs, Hcap, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iunfold ownDec at Hdd
        icases Hdd with ⟨%s0', %dq0', Hd, Hs0⟩
        iexists _, (ps ++ [{ Key' := k, Val' := v }]), s1, r3, ok3, s0', dq0'
        iframe
        ipureintro
        intro h3
        obtain ⟨h2, e3⟩ := H3 h3
        obtain ⟨-, e2⟩ := H2 h2
        rw [Hok rfl, e2, e3, kvsBody_snoc]
        simp only [List.append_assoc]
      · (try wp_auto)
        try simp only [decide_eq_false hc, val_false_ne_true, decide_false, Bool.false_eq_true, ↓reduceIte]
        simp only [_root_.decide_true, ↓reduceIte]
        (try wp_auto)
        ihave Hdd : ownDec d r true $$ [Hd Hs0]
        · unfold ownDec; iexists s0, dq0; iframe
        imod ownSlice_persist s _ _ $$ Hs with #Hs
        wp_apply wp_Done d r true $$ [Hdd] as %dn %Hdn
        · iframe
        (try wp_auto)
        iapply HΦ'
        iintro %hdn
        obtain ⟨-, hnil⟩ := Hdn hdn
        have hb := Hok rfl
        rw [hnil] at hb
        obtain ⟨rfl, hlen⟩ := kvsBytes_dec hb
        iexists s
        iframe #
        ipureintro
        exact ⟨rfl, hlen⟩
  isplitr
  · -- EncOut
    iintro %v %o !> %Φ' ⟨%sl, ⟨%Hv, %Hlen⟩, #Hsl⟩ HΦ'
    subst Hv
    ihave %Hsl_len := ownSlice_len _ _ _ $$ Hsl
    wp_auto
    ihave He : ownEnc «$r0_ptr» [] $$ [«$r0»]
    · unfold ownEnc
      iexists slice.nil
      iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    wp_apply wp_EncInt _ _ sl.len $$ [He] as He
    · iframe
    (try wp_auto)
    isimp only [List.nil_append] at He
    ihave IH : (∃ (j : Nat) (pv : wrec),
        "i" ∷ i_ptr ↦ W64 j ∗ "r" ∷ r_ptr ↦ pv ∗
        "He" ∷ ownEnc «$r0_ptr» (encU64 sl.len ++ recsBody (o.take j)) ∗
        "%Hj" ∷ ⌜j ≤ o.length⌝ : IProp GF) $$ [i r He]
    · iexists 0, _
      rw [List.take_zero, recsBody_nil, List.append_nil]
      iframe
      ipureintro; omega
    wp_for IH
    by_cases hj : j < o.length
    · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
      simp only [decide_eq_true hc, ↓reduceIte]
      (try wp_auto)
      have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      try simp only [h0, hc, _root_.and_self, ↓reduceIte]
      try simp only [decide_eq_true_eq, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
      obtain ⟨x, hx⟩ : ∃ x, o[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
      wp_apply (wp_load_slice_index sl (sint.Z (W64 (j : Int))) o DFrac.discard x h0) $$ [] as -
      · iframe #; ipureintro; rw [hsj]; exact hx
      (try wp_auto)
      wp_apply wp_EncI64 _ _ x.Rev' $$ [He] as He
      · iframe
      (try wp_auto)
      wp_apply wp_EncStr _ _ x.Key' $$ [He] as He
      · iframe
      (try wp_auto)
      wp_apply wp_EncStr _ _ x.Val' $$ [He] as He
      · iframe
      (try wp_auto)
      wp_for_post
      iframe
      iexists (j + 1), x
      have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
      have hb : encU64 sl.len ++ recsBody (o.take (j + 1)) =
          encU64 sl.len ++ recsBody (o.take j) ++ encU64 x.Rev' ++ encStr x.Key' ++ encStr x.Val' := by
        rw [recsBody_take_succ _ _ _ hx]; simp only [List.append_assoc]
      rw [hw, hb]
      iframe
      ipureintro; omega
    · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
      simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
      have hjl : j = o.length := by omega
      subst hjl
      rw [List.take_length]
      (try wp_auto)
      iunfold ownEnc at He
      icases He with ⟨%s, He, Hs, -⟩
      (try wp_auto)
      try simp only [val_false_ne_true, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      try simp only [decide_eq_true_eq, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      iapply HΦ'
      have e : capped (recsBytes o) = encU64 sl.len ++ recsBody o := by
        rw [capped_of _ Hlen, recsBytes_eq]
        obtain ⟨h1, h2⟩ := Hsl_len
        congr 2
        word
      rw [e]
      iexact Hs
  isplitr
  · -- DecOut
    iintro %o %b %dq !> %Φ' Hb HΦ'
    wp_auto
    wp_apply wp_NewDec b _ dq $$ [Hb] as %d Hd
    · iframe
    (try wp_auto)
    wp_apply wp_DecInt d _ true $$ [Hd] as %n Hd
    · iframe
    icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r1, %ok1, Hd, %H1⟩
    (try wp_auto)
    ihave IH : (∃ (j : w64) (rs : List wrec) (s : GoSlice) (r : List w8) (ok : Bool) (s0 : GoSlice)
        (dq0 : DFrac),
        "i" ∷ i_ptr ↦ j ∗ "rs" ∷ rs_ptr ↦ s ∗ "Hs" ∷ s ↦* rs ∗
        "Hcap" ∷ ownSliceCap wrec s (DFrac.own 1) ∗
        "Hd" ∷ d ↦ ({ B' := s0, Ok' := ok } : Dec) ∗ "Hs0" ∷ s0 ↦*{dq0} r ∗
        "%Hok" ∷ ⌜ok = true → capped (recsBytes o) = encU64 n ++ recsBody rs ++ r⌝ : IProp GF)
        $$ [i rs Hd]
    · iunfold ownDec at Hd
      icases Hd with ⟨%s0, %dq0, Hd, Hs0⟩
      iexists W64 0, [], slice.nil, r1, ok1, s0, dq0
      iframe
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      ipureintro
      intro h
      obtain ⟨-, h⟩ := H1 h
      rw [h, recsBody_nil, List.append_nil]
    wp_for IH
    cases ok
    · -- the flag is false: the loop ends
      (try wp_auto)
      try simp only [val_false_ne_true, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      try simp only [decide_eq_true_eq, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      ihave Hdd : ownDec d r false $$ [Hd Hs0]
      · unfold ownDec; iexists s0, dq0; iframe
      wp_apply wp_Done d r false $$ [Hdd] as %dn %Hdn
      · iframe
      (try wp_auto)
      iapply HΦ'
      iintro %hdn
      exact absurd (Hdn hdn).1 Bool.false_ne_true
    · by_cases hc : sint.Z j < sint.Z n
      · (try wp_auto)
        simp only [decide_eq_true hc]
        simp only [_root_.decide_true, ↓reduceIte]
        (try wp_auto)
        ihave Hdd : ownDec d r true $$ [Hd Hs0]
        · unfold ownDec; iexists s0, dq0; iframe
        wp_apply wp_DecI64 d r true $$ [Hdd] as %rv Hdd
        · iframe
        icases decPost_elim _ _ _ _ _ $$ Hdd with ⟨%r2, %ok2, Hdd, %H2⟩
        (try wp_auto)
        wp_apply wp_DecStr d r2 ok2 $$ [Hdd] as %k Hdd
        · iframe
        icases decPost_elim _ _ _ _ _ $$ Hdd with ⟨%r3, %ok3, Hdd, %H3⟩
        (try wp_auto)
        wp_apply wp_DecStr d r3 ok3 $$ [Hdd] as %v Hdd
        · iframe
        icases decPost_elim _ _ _ _ _ $$ Hdd with ⟨%r4, %ok4, Hdd, %H4⟩
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl', -⟩
        wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl'] as %s1 ⟨Hs, Hcap, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iunfold ownDec at Hdd
        icases Hdd with ⟨%s0', %dq0', Hd, Hs0⟩
        iexists _, (rs ++ [{ Rev' := rv, Key' := k, Val' := v }]), s1, r4, ok4, s0', dq0'
        iframe
        ipureintro
        intro h4
        obtain ⟨h3, e4⟩ := H4 h4
        obtain ⟨h2, e3⟩ := H3 h3
        obtain ⟨-, e2⟩ := H2 h2
        rw [Hok rfl, e2, e3, e4, recsBody_snoc]
        simp only [List.append_assoc]
      · (try wp_auto)
        try simp only [decide_eq_false hc, val_false_ne_true, decide_false, Bool.false_eq_true, ↓reduceIte]
        simp only [_root_.decide_true, ↓reduceIte]
        (try wp_auto)
        ihave Hdd : ownDec d r true $$ [Hd Hs0]
        · unfold ownDec; iexists s0, dq0; iframe
        imod ownSlice_persist s _ _ $$ Hs with #Hs
        wp_apply wp_Done d r true $$ [Hdd] as %dn %Hdn
        · iframe
        (try wp_auto)
        iapply HΦ'
        iintro %hdn
        obtain ⟨-, hnil⟩ := Hdn hdn
        have hb := Hok rfl
        rw [hnil] at hb
        obtain ⟨rfl, hlen⟩ := recsBytes_dec hb
        iexists s
        iframe #
        ipureintro
        exact ⟨rfl, hlen⟩
  isplitr
  · -- the unknown answers' encoding: a report has none
    iintro %i %v %h
    exact False.elim h
  · iintro %i %v %b %dq %h
    exact False.elim h

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
