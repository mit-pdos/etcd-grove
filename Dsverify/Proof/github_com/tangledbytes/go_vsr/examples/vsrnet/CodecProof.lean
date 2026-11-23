/-
`Codec()` (kit.go) is the far side's store's codec (`codecOk (kvR g)`): an input as its kind, its
key's length, its key and value; an output as three flags and its value (notes/dsv-vr.md, step 3).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ModelProof
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost.Impl

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem inFields_bnd (i : KIn) :
    (inFields i.1).2.1.length < 256 ∧ (inFields i.1).2.2.length < 2 ^ 16 := by
  obtain ⟨i, -, hb, hk⟩ := i
  cases i <;> simp only [InputBounded] at hb <;> simp only [inFields, List.length_nil] at hk ⊢ <;> omega

/-- An output the codec meets is a short `Out`. -/
theorem outOk_out (g : GN) (x : GoInterface) (h : RBase.outOk (kvR (GF := GF) (Gg := hG.goose_globalGS) g) x) :
    ∃ u d f w, w.length < 2 ^ 16 ∧ x = outVal u d f w := by
  rcases h with ⟨o, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨_, _, _, _, outFields_bnd o, rfl⟩
  · exact ⟨true, false, false, [], by simp, rfl⟩

/-- `Codec()`: the map's codec. -/
abbrev Codec.spec : Prop :=
  ∀ g : GN,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      codecOk (kvR (GF := GF) (Gg := hG.goose_globalGS) g) cd }}

theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro g
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk kvR
  simp only
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' - HΦ'
    rw [inV_eq i]
    obtain ⟨hk, hv⟩ := inFields_bnd i
    unfold encInB
    generalize inFields i.1 = p at hk hv
    obtain ⟨u, k, v⟩ := p
    simp only at hk hv ⊢
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_apply (wp_slice_make3 (V := w8) (W64 2) (W64 2 + W64 k.length + W64 v.length) (by word))
      as %b ⟨Hb, Hcap, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    cases u
    · wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      rw [ite_eq_left h1]
      wp_apply wp_store_slice_index b (sint.Z (W64 1)) _ (W8 (sint.Z (W64 k.length))) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_apply wp_string_to_bytes as %sk ⟨Hsk, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsk] as %b2 ⟨Hb2, Hcap2, -⟩
      wp_apply wp_string_to_bytes as %sv ⟨Hsv, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb2 $Hcap2 $Hsv] as %b3 ⟨Hb3, -, -⟩
      iapply HΦ'
      have e : W8 (sint.Z (W64 k.length)) = W8 k.length := by word
      rw [e]
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [show W8 0 :: W8 k.length :: (k ++ v) =
          (List.replicate 2 (zero_val w8)).set 1 (W8 k.length) ++ k ++ v by
            simp [List.replicate]; rfl]
      iexact Hb3
    · wp_auto
      rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      rw [ite_eq_left h1]
      wp_apply wp_store_slice_index b (sint.Z (W64 1)) _ (W8 (sint.Z (W64 k.length))) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_apply wp_string_to_bytes as %sk ⟨Hsk, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsk] as %b2 ⟨Hb2, Hcap2, -⟩
      wp_apply wp_string_to_bytes as %sv ⟨Hsv, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb2 $Hcap2 $Hsv] as %b3 ⟨Hb3, -, -⟩
      iapply HΦ'
      have e : W8 (sint.Z (W64 k.length)) = W8 k.length := by word
      rw [e]
      simp only [↓reduceIte]
      rw [show W8 1 :: W8 k.length :: (k ++ v) =
          ((List.replicate 2 (zero_val w8)).set 0 (W8 1)).set 1 (W8 k.length) ++ k ++ v by
            simp [List.replicate]]
      iexact Hb3
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    rw [inV_eq i]
    obtain ⟨hk, hv⟩ := inFields_bnd i
    unfold encInB at *
    generalize inFields i.1 = p at hk hv
    obtain ⟨u, k, v⟩ := p
    simp only at hk hv ⊢
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    simp only [List.length_cons, List.length_append] at Hlen
    have hb2 : sint.Z b.len = 2 + k.length + v.length := by
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg Hlen.2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by constructor <;> word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by constructor <;> word
    wp_auto
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 2) by word)]
    wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [decide_eq_false (show ¬ uint.Z (W8 1) < uint.Z (if u = true then W8 1 else W8 0) by
      cases u <;> decide)]
    wp_auto
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (W8 k.length) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    have hk8 : uint.Z (W8 k.length) = k.length := by
      exact uint_Z_W8 _ (by omega) (by omega)
    have hkk : W64 2 + W64 (uint.Z (W8 k.length)) = W64 (2 + k.length) := by rw [hk8]; word
    rw [hkk]
    have hblu : uint.Z b.len = 2 + k.length + v.length := by word
    rw [decide_eq_false (show ¬ uint.Z b.len < uint.Z (W64 (2 + k.length)) by word)]
    wp_auto
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (W8 k.length) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [hkk]
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z (W64 (2 + k.length)) ∧
      sint.Z (W64 (2 + k.length)) ≤ sint.Z b.cap by refine ⟨by word, by word, by word⟩)]
    icases (ownSlice_slice (W64 2) (W64 (2 + k.length)) b dq _ ⟨by word, by word, by word⟩).1 $$ Hb
      with ⟨-, Hk, Hv⟩
    have hs1 : subslice (sint.nat (W64 2)) (sint.nat (W64 (2 + k.length)))
        ((if u = true then W8 1 else W8 0) :: W8 k.length :: (k ++ v)) = k := by
      have e1 : sint.nat (W64 2) = 2 := by word
      have e2 : sint.nat (W64 (2 + k.length)) = 2 + k.length := by word
      rw [e1, e2, show 2 + k.length = k.length + 1 + 1 by omega]
      simp only [subslice, List.take_succ_cons, List.drop_succ_cons, List.drop_zero, List.take_left]
    have hs2 : List.drop (sint.nat (W64 (2 + k.length)))
        ((if u = true then W8 1 else W8 0) :: W8 k.length :: (k ++ v)) = v := by
      have e2 : sint.nat (W64 (2 + k.length)) = 2 + k.length := by word
      rw [e2, show 2 + k.length = k.length + 1 + 1 by omega]
      simp only [List.drop_succ_cons, List.drop_left]
    rw [hs1, hs2]
    wp_apply wp_bytes_to_string $$ [Hk] as Hk
    · iexact Hk
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (2 + k.length)) ∧ sint.Z (W64 (2 + k.length)) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap by refine ⟨by word, by word, Hwf.2⟩)]
    wp_apply wp_bytes_to_string $$ [Hv] as Hv
    · iexact Hv
    iapply HΦ'
    ipureintro
    intro _
    cases u <;> rfl
  isplitr
  · -- EncOut
    iintro %x %Hx
    obtain ⟨u, d, f, w, hw, rfl⟩ := outOk_out g x Hx
    iintro !> %Φ' - HΦ'
    rw [encOutV_outVal _ _ _ _ hw]
    unfold outVal
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_apply (wp_slice_make3 (V := w8) (W64 3) (W64 3 + W64 w.length) (by word))
      as %b ⟨Hb, Hcap, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have hl : sint.Z b.len = 3 := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by constructor <;> word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by constructor <;> word
    have h2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z b.len := by constructor <;> word
    cases u <;> cases d <;> cases f <;>
    · wp_auto
      repeat
        first
          | (rw [ite_eq_left h0]
             wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
             · iframe Hb; ipureintro; simp only [List.length_set, List.length_replicate]; word
             try wp_auto)
          | (rw [ite_eq_left h1]
             wp_apply wp_store_slice_index b (sint.Z (W64 1)) _ (W8 1) $$ [Hb] as Hb
             · iframe Hb; ipureintro; simp only [List.length_set, List.length_replicate]; word
             try wp_auto)
          | (rw [ite_eq_left h2]
             wp_apply wp_store_slice_index b (sint.Z (W64 2)) _ (W8 1) $$ [Hb] as Hb
             · iframe Hb; ipureintro; simp only [List.length_set, List.length_replicate]; word
             try wp_auto)
      wp_apply wp_string_to_bytes as %sw ⟨Hsw, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsw] as %b2 ⟨Hb2, -, -⟩
      iapply HΦ'
      have hz : zero_val w8 = W8 0 := rfl
      simp [encOutB, List.replicate, hz]
      iexact Hb2
  isplitr
  · -- DecOut
    iintro %x %b %dq %Hx
    obtain ⟨u, d, f, w, hw, rfl⟩ := outOk_out g x Hx
    iintro !> %Φ' Hb HΦ'
    rw [encOutV_outVal _ _ _ _ hw]
    unfold encOutB
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    simp only [List.length_cons] at Hlen
    have hb3 : sint.Z b.len = 3 + w.length := by
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg Hlen.2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by constructor <;> word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by constructor <;> word
    have h2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z b.len := by constructor <;> word
    have hbit : ∀ c : Bool, ¬ uint.Z (W8 1) < uint.Z (if c = true then W8 1 else W8 0) := by
      intro c; cases c <;> decide
    wp_auto
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 3) by word)]
    wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [decide_eq_false (hbit u)]
    try wp_auto
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (if d then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [decide_eq_false (hbit d)]
    try wp_auto
    rw [ite_eq_left h2]
    wp_apply wp_load_slice_index b (sint.Z (W64 2)) _ dq (if f then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [decide_eq_false (hbit f)]
    try wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    try wp_auto
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (if d then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    try wp_auto
    rw [ite_eq_left h2]
    wp_apply wp_load_slice_index b (sint.Z (W64 2)) _ dq (if f then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    try wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by word, by word, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 3) b dq _ ⟨by word, by word⟩).1 $$ Hb with ⟨-, Hb2⟩
    rw [show sint.nat (W64 3) = 0 + 1 + 1 + 1 from rfl, List.drop_succ_cons, List.drop_succ_cons,
      List.drop_succ_cons, List.drop_zero]
    wp_apply wp_bytes_to_string $$ [Hb2] as Hb2
    · iexact Hb2
    iapply HΦ'
    ipureintro
    intro _
    cases u <;> cases d <;> cases f <;> rfl
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    obtain ⟨i, -⟩ := i
    unfold inV
    wp_auto
    cases i <;> (simp only [kvB, inFields]; iapply HΦ'; itrivial)
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

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
