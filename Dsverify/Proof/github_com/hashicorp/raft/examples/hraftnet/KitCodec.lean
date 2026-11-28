/-
`Codec()` (kit.go) and its helpers, proved over the real code (notes/dsv-hraft.md, S5): an input is its
put flag, its way and its value (length first); an output its unknown and found flags and its value.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.KitCodecDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

theorem flag.wp_proof : flag.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  cases x <;> wp_auto <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iapply HΦ <;> itrivial

theorem encStr.wp_proof : encStr.spec (GF := GF) (hG := hG) := by
  intro b bs s hs
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  try wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  wp_apply wp_slice_literal (V := w8) [W8 (sint.Z (W64 s.length))]
  isplitr
  · ipureintro; rfl
  iintro %lp ⟨Hl, Hlc⟩
  try wp_auto
  wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hl] as %b2 ⟨Hb2, Hcap2, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes as %ss ⟨Hss, -⟩
  wp_apply wp_slice_append (V := w8) $$ [$Hb2 $Hcap2 $Hss] as %b3 ⟨Hb3, Hcap3, -⟩
  try wp_auto
  have e : W8 (sint.Z (W64 (s.length : Int))) = W8 s.length := by word
  iapply HΦ
  rw [← e, show bs ++ W8 (sint.Z (W64 (s.length : Int))) :: s =
    bs ++ [W8 (sint.Z (W64 (s.length : Int)))] ++ s by simp]
  iframe

theorem decStr.wp_proof : decStr.spec (GF := GF) (hG := hG) := by
  intro b dq v r hv
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  simp only [List.length_cons, List.length_append] at Hlen
  have hbl : sint.Z b.len = 1 + v.length + r.length := by
    have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg Hlen.2
    omega
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by constructor <;> word
  have hv8 : uint.Z (W8 v.length) = v.length := uint_Z_W8 _ (by omega) (by omega)
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 1) by word)]
  wp_auto
  rw [ite_eq_left h0]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (W8 v.length) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  rw [hv8]
  have hhi : W64 1 + W64 (v.length : Int) = W64 (1 + v.length) := by word
  rw [hhi, decide_eq_false (show ¬ uint.Z b.len < uint.Z (W64 (1 + v.length : Int)) by word)]
  wp_auto
  rw [ite_eq_left h0]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (W8 v.length) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  rw [hv8, hhi]
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (W64 (1 + v.length : Int)) ∧
    sint.Z (W64 (1 + v.length : Int)) ≤ sint.Z b.cap by refine ⟨by word, by word, by word⟩)]
  icases (ownSlice_slice (W64 1) (W64 (1 + v.length)) b dq _ ⟨by word, by word, by word⟩).1 $$ Hb
    with ⟨Hp, Hv, Hr⟩
  have hs1 : subslice (sint.nat (W64 1)) (sint.nat (W64 (1 + v.length : Int)))
      (W8 v.length :: (v ++ r)) = v := by
    have e1 : sint.nat (W64 1) = 1 := by word
    have e2 : sint.nat (W64 (1 + v.length : Int)) = 1 + v.length := by word
    rw [e1, e2, show 1 + v.length = v.length + 1 by omega]
    simp only [subslice, List.take_succ_cons, List.drop_succ_cons, List.drop_zero, List.take_left]
  have hs2 : List.drop (sint.nat (W64 (1 + v.length : Int))) (W8 v.length :: (v ++ r)) = r := by
    have e2 : sint.nat (W64 (1 + v.length : Int)) = 1 + v.length := by word
    rw [e2, show 1 + v.length = v.length + 1 by omega]
    simp only [List.drop_succ_cons, List.drop_left]
  rw [hs1, hs2]
  ihave %Hrl := ownSlice_len _ _ _ $$ Hr
  wp_apply wp_bytes_to_string $$ [Hv] as Hv
  · iexact Hv
  wp_auto
  rw [hhi]
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (1 + v.length : Int)) ∧ sint.Z (W64 (1 + v.length : Int)) ≤
    sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap by refine ⟨by word, by word, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  isplitl
  · iapply (ownSlice_slice (W64 1) (W64 (1 + v.length)) b dq _ ⟨by word, by word, by word⟩).2
    rw [hs1, hs2]
    iframe
  · ipureintro
    rw [Hrl.1]
    exact (Int.toNat_of_nonneg Hrl.2).symm

theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro g
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk regR
  simp only
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' - HΦ'
    obtain ⟨⟨p, w, v⟩, hw, hv⟩ := i
    simp only at hw hv
    unfold inV encInB
    simp only
    wp_auto
    wp_apply flag.wp_proof
    try wp_auto
    wp_apply wp_slice_literal (V := w8) [if p then W8 1 else W8 0, W8 (uint.Z w)]
    isplitr
    · ipureintro; rfl
    iintro %lp ⟨Hl, Hlc⟩
    try wp_auto
    wp_apply encStr.wp_proof _ _ v hv $$ [$Hl $Hlc] as %b' ⟨Hb', -⟩
    iapply HΦ'
    simp only [List.cons_append, List.nil_append] at *
    iexact Hb'
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    obtain ⟨⟨p, w, v⟩, hw, hv⟩ := i
    simp only at hw hv
    unfold inV encInB
    simp only
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    simp only [List.length_cons] at Hlen
    have hbl : sint.Z b.len = 3 + v.length := by
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg Hlen.2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by constructor <;> word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by constructor <;> word
    have hw8 : uint.Z (W8 (uint.Z w)) = uint.Z w := uint_Z_W8 _ (by word) (by word)
    have hbit : ∀ c : Bool, ¬ uint.Z (W8 1) < uint.Z (if c = true then W8 1 else W8 0) := by
      intro c; cases c <;> decide
    wp_auto
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 2) by word)]
    wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if p then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [decide_eq_false (hbit p)]
    try wp_auto
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (W8 (uint.Z w)) (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [decide_eq_false (show ¬ uint.Z (W8 2) < uint.Z (W8 (uint.Z w)) by rw [hw8]; word)]
    try wp_auto
    have h2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z b.len := ⟨by word, by word⟩
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨h2.1, h2.2, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 2) b dq _ h2).1 $$ Hb with ⟨Hp, Hs⟩
    have hd2 : List.drop (sint.nat (W64 2))
        ((if p = true then W8 1 else W8 0) :: W8 (uint.Z w) :: W8 v.length :: v) =
        W8 v.length :: (v ++ []) := by
      rw [show sint.nat (W64 2) = 0 + 1 + 1 from rfl, List.drop_succ_cons, List.drop_succ_cons,
        List.drop_zero, List.append_nil]
    rw [hd2]
    wp_apply decStr.wp_proof _ dq v [] hv $$ [$Hs] as %rs ⟨Hs, %Hbl'⟩
    have hb0 : rs.len = W64 0 := by simp at Hbl'; word
    rw [hb0]
    wp_auto
    rw [← hd2]
    ihave Hb := (ownSlice_split_all (W64 2) b dq _ h2).2 $$ [$Hp $Hs]
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if p then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    try wp_auto
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (W8 (uint.Z w)) (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    try wp_auto
    iapply HΦ'
    ipureintro
    intro _
    have hw'' : BitVec.ofNat 64 (BitVec.toNat w % 256) = w := by
      have : BitVec.toNat w < 256 := by have := hw; word
      rw [Nat.mod_eq_of_lt this]; simp
    cases p <;> simp [hw'']
  isplitr
  · -- EncOut
    iintro %x %Hx
    obtain ⟨u, f, v, hv, rfl⟩ := outOk_outVal g x Hx
    iintro !> %Φ' - HΦ'
    rw [encOutV_outVal _ _ _ hv]
    unfold outVal encOutB
    wp_auto
    wp_apply flag.wp_proof
    wp_apply flag.wp_proof
    try wp_auto
    wp_apply wp_slice_literal (V := w8) [if u then W8 1 else W8 0, if f then W8 1 else W8 0]
    isplitr
    · ipureintro; rfl
    iintro %lp ⟨Hl, Hlc⟩
    try wp_auto
    wp_apply encStr.wp_proof _ _ v hv $$ [$Hl $Hlc] as %b' ⟨Hb', -⟩
    iapply HΦ'
    simp only [List.cons_append, List.nil_append] at *
    iexact Hb'
  isplitr
  · -- DecOut
    iintro %x %b %dq %Hx
    obtain ⟨u, f, v, hv, rfl⟩ := outOk_outVal g x Hx
    iintro !> %Φ' Hb HΦ'
    rw [encOutV_outVal _ _ _ hv]
    unfold encOutB
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    simp only [List.length_cons] at Hlen
    have hbl : sint.Z b.len = 3 + v.length := by
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg Hlen.2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by constructor <;> word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by constructor <;> word
    have hbit : ∀ c : Bool, ¬ uint.Z (W8 1) < uint.Z (if c = true then W8 1 else W8 0) := by
      intro c; cases c <;> decide
    wp_auto
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 2) by word)]
    wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [decide_eq_false (hbit u)]
    try wp_auto
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (if f then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [decide_eq_false (hbit f)]
    try wp_auto
    have h2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z b.len := ⟨by word, by word⟩
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨h2.1, h2.2, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 2) b dq _ h2).1 $$ Hb with ⟨Hp, Hs⟩
    have hd2 : List.drop (sint.nat (W64 2))
        ((if u = true then W8 1 else W8 0) :: (if f = true then W8 1 else W8 0) :: W8 v.length :: v) =
        W8 v.length :: (v ++ []) := by
      rw [show sint.nat (W64 2) = 0 + 1 + 1 from rfl, List.drop_succ_cons, List.drop_succ_cons,
        List.drop_zero, List.append_nil]
    rw [hd2]
    wp_apply decStr.wp_proof _ dq v [] hv $$ [$Hs] as %rs ⟨Hs, %Hbl'⟩
    have hb0 : rs.len = W64 0 := by simp at Hbl'; word
    rw [hb0]
    wp_auto
    rw [← hd2]
    ihave Hb := (ownSlice_split_all (W64 2) b dq _ h2).2 $$ [$Hp $Hs]
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    try wp_auto
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (if f then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    try wp_auto
    iapply HΦ'
    ipureintro
    intro _
    unfold outVal
    cases u <;> cases f <;> simp
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    obtain ⟨⟨p, w, v⟩, -⟩ := i
    unfold inV
    wp_auto
    cases p <;> (simp only [regB]; iapply HΦ'; itrivial)
  isplitr
  · -- Unknown
    iintro %i
    iintro !> %Φ' - HΦ'
    unfold unkV outVal
    wp_auto
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' - HΦ'
    unfold outV outVal
    wp_auto
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' - HΦ'
    unfold unkV outVal
    wp_auto
    iapply HΦ'
    itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
