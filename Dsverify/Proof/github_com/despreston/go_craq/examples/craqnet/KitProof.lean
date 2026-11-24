/-
The proofs of the craq kit's codec and generator (`kit.go`, notes/dsv-craq.md): `Codec.wp_proof`,
`Gen.wp_proof`, over `KitDefs.lean`'s helpers.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec EtcdGrove.lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n _
  wp_apply wp_digit
  wp_if_destruct
  · wp_apply wp_digit
    wp_apply wp_digit
    iapply HΦ
    imodintro
    ipureintro
    refine ⟨⟨.put _ _, ?_⟩, rfl⟩
    simp [inOk, keyOk]
  · iapply HΦ
    imodintro
    ipureintro
    refine ⟨⟨.get _, ?_⟩, rfl⟩
    simp [inOk, keyOk]

theorem Codec.wp_proof [go.BasicIntoValInj] : Codec.spec (GF := GF) (hG := hG) := by
  intro γ
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
    obtain ⟨p, k, v, hk, hv, hiv, he⟩ : ∃ (p : Bool) (k v : GoString), k.length < 256 ∧
        v.length < 256 ∧ ivK i = inV p k v ∧ encInB i = flagB p :: (encS k ++ encS v) := by
      obtain ⟨k | ⟨k, v⟩, hi⟩ := i
      · exact ⟨false, k, [], keyOk_lt hi, by simp, rfl, rfl⟩
      · exact ⟨true, k, v, keyOk_lt hi.1, hi.2, rfl, rfl⟩
    rw [hiv, he]
    wp_auto
    wp_apply wp_flag
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, Hcap⟩
    wp_auto
    wp_apply wp_encStr _ _ k hk $$ [$Hsl $Hcap] as %b1 ⟨Hb1, Hcap1⟩
    wp_apply wp_encStr _ _ v hv $$ [$Hb1 $Hcap1] as %b2 ⟨Hb2, Hcap2⟩
    iapply HΦ'
    simp only [List.cons_append, List.nil_append]
    iexact Hb2
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    obtain ⟨p, k, v, hk, hv, hiv, he⟩ : ∃ (p : Bool) (k v : GoString), k.length < 256 ∧
        v.length < 256 ∧ ivK i = inV p k v ∧ encInB i = flagB p :: (encS k ++ encS v) := by
      obtain ⟨k | ⟨k, v⟩, hi⟩ := i
      · exact ⟨false, k, [], keyOk_lt hi, by simp, rfl, rfl⟩
      · exact ⟨true, k, v, keyOk_lt hi.1, hi.2, rfl, rfl⟩
    rw [hiv, he]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hbl := sint_len_eq Hlen
    simp only [encS, List.cons_append, List.length_cons, List.length_append] at hbl
    push_cast at hbl
    have hz0 : sint.Z (W64 0) = 0 := rfl
    have hz1 : sint.Z (W64 1) = 1 := rfl
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by omega
    wp_auto
    wp_if_destruct
    · exfalso; omega
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (flagB p) (by omega) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; cases p <;> simp only [flagB, Bool.false_eq_true, ↓reduceIte] at Hif <;> word
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by omega, by omega, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 1) b dq _ ⟨by omega, by omega⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
    rw [show sint.nat (W64 1) = 1 from rfl, List.drop_one, List.tail_cons]
    wp_apply wp_decStr _ dq k _ hk $$ Hb2 as %r Hr
    simp only [List.take_succ_cons, List.take_zero]
    rw [show encS v = encS v ++ [] by simp]
    wp_apply wp_decStr _ dq v [] hv $$ Hr as %r2 Hr2
    ihave %Hr2l := ownSlice_len _ _ _ $$ Hr2
    wp_if_destruct
    · rw [ite_eq_left h0]
      rw [← sliceIndexRef_slice0 b (W64 1) (sint.Z (W64 0))]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ dq (flagB p) (by omega) $$ [Hb1] as Hb1
      · iframe Hb1; ipureintro; rfl
      wp_auto
      iapply HΦ'
      ipureintro
      intro _
      rw [flagB_dec p]
    iapply HΦ'; ipureintro; simp
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨u, f, w, rfl⟩ := outOk_outV γ v Hv
    iintro !> %Φ' - HΦ'
    rw [encOutV_outV, show encOutB u f w.1 = [flagB u, flagB f] ++ encS w.1 from rfl]
    have hw := w.2
    wp_auto
    wp_apply wp_flag
    wp_apply wp_flag
    wp_apply wp_slice_literal (V := w8) [_, _]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, Hcap⟩
    wp_auto
    wp_apply wp_encStr _ _ w.1 hw $$ [$Hsl $Hcap] as %b1 ⟨Hb1, -⟩
    iapply HΦ'
    iexact Hb1
  isplitr
  · -- DecOut
    iintro %v %b %dq %Hv
    obtain ⟨u, f, w, rfl⟩ := outOk_outV γ v Hv
    iintro !> %Φ' Hb HΦ'
    rw [encOutV_outV, show encOutB u f w.1 = flagB u :: flagB f :: encS w.1 from rfl]
    have hw := w.2
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hbl := sint_len_eq Hlen
    simp only [encS, List.length_cons] at hbl
    push_cast at hbl
    have hz0 : sint.Z (W64 0) = 0 := rfl
    have hz1 : sint.Z (W64 1) = 1 := rfl
    have hz2 : sint.Z (W64 2) = 2 := rfl
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by omega
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by omega
    wp_auto
    wp_if_destruct
    · exfalso; omega
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (flagB u) (by omega) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; cases u <;> simp only [flagB, Bool.false_eq_true, ↓reduceIte] at Hif <;> word
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (flagB f) (by omega) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; cases f <;> simp only [flagB, Bool.false_eq_true, ↓reduceIte] at Hif <;> word
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by omega, by omega, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 2) b dq _ ⟨by omega, by omega⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
    rw [show sint.nat (W64 2) = 2 from rfl]
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
    rw [show encS w.1 = encS w.1 ++ [] by simp]
    wp_apply wp_decStr _ dq w.1 [] hw $$ Hb2 as %r Hr
    wp_if_destruct
    · rw [ite_eq_left h0]
      rw [← sliceIndexRef_slice0 b (W64 2) (sint.Z (W64 0))]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ dq (flagB u) (by omega) $$ [Hb1] as Hb1
      · iframe Hb1; ipureintro; rfl
      wp_auto
      rw [ite_eq_left h1]
      rw [← sliceIndexRef_slice0 b (W64 2) (sint.Z (W64 1))]
      wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ dq (flagB f) (by omega) $$ [Hb1] as Hb1
      · iframe Hb1; ipureintro; rfl
      wp_auto
      iapply HΦ'
      ipureintro
      intro _
      rw [flagB_dec u, flagB_dec f]
    iapply HΦ'; ipureintro; simp
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    obtain ⟨k | ⟨k, v⟩, hi⟩ := i
    · wp_auto
      rw [show (!kvB.isWrite ⟨KvInput.get k, hi⟩) = true from rfl]
      iapply HΦ'
      itrivial
    · wp_auto
      rw [show (!kvB.isWrite ⟨KvInput.put k v, hi⟩) = false from rfl]
      iapply HΦ'
      itrivial
  isplitr
  · -- Unknown
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' - HΦ'
    rcases o with (_ | x) | _
    · wp_auto
      iapply HΦ'
      itrivial
    · wp_auto
      iapply HΦ'
      itrivial
    · wp_auto
      iapply HΦ'
      itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
