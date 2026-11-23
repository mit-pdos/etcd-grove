/-
The proofs of the craq kit's codec, generator and small helpers (`kit.go`, notes/dsv-craq.md):
`Codec.wp_proof`, `Gen.wp_proof`, and `wp_ServerAddrs`, `wp_ClientAddrs`, `wp_ConfAddrs`,
`wp_attempt`, `wp_digit`; the codec's helpers `wp_flag`, `wp_encStr`, `wp_decStr` and
`encOutV_outV`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ModelProof
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section inj
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : github_com.despreston.go_craq.examples.craqnet.Assumptions]

/-- `Out{u, f, w}`'s bytes. -/
theorem encOutV_outV (u f : Bool) (w : Str8) : encOutV (outV u f w.1) = encOutB u f w.1 := by
  unfold encOutV
  split
  · rename_i h
    have hs := Classical.choose_spec h
    obtain ⟨h1, h2, h3⟩ := outV_inj hs
    rw [← h1, ← h2, ← h3]
  · rename_i h
    exact absurd ⟨(u, f, w), rfl⟩ h

end inj

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

/-- `ServerAddrs()` returns a new slice of the server machines' addresses. -/
theorem wp_ServerAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.ServerAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* serverAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) serverAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `ClientAddrs()` returns a new slice of the client machines' addresses. -/
theorem wp_ClientAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.ClientAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* clientAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) clientAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `ConfAddrs()` returns a new slice of the configuration addresses. -/
theorem wp_ConfAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.ConfAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* confAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) confAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `attempt()`: some duration. -/
theorem wp_attempt :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.attempt)) (Val #()))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

/-- `digit(n)`: the one-byte string of `n`'s last decimal digit (no package state needed: `Gen`'s
spec, `genSpec`, gives none). -/
theorem wp_digit (n : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.digit)) (Val #n))
    {{ RET #([W8 (48 + uint.Z n % 10)] : GoString); True }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := w8) [_]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  wp_apply wp_bytes_to_string $$ Hsl as Hsl
  rw [show W8 (uint.Z (W64 48 + n % W64 10)) = W8 (48 + uint.Z n % 10) by word]
  iapply HΦ
  itrivial

/-- `flag(x)`: `flagB x`. -/
theorem wp_flag (x : Bool) :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.flag)) (Val #x))
    {{ RET #(flagB x); True }} := by
  wp_start
  wp_auto
  cases x
  · wp_auto
    rw [show flagB false = W8 0 from rfl]
    iapply HΦ
    itrivial
  · wp_auto
    rw [show flagB true = W8 1 from rfl]
    iapply HΦ
    itrivial

/-- `encStr(b, s)`: `b` with `encS s` appended. -/
theorem wp_encStr (b : GoSlice) (l : List w8) (str : GoString) (hs : str.length < 256) :
    {{ (b ↦* l ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.encStr)) (Val #b))
        (Val #str))
    {{ (b' : GoSlice), RET #b'; b' ↦* (l ++ encS str) ∗ ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  wp_apply wp_slice_literal (V := w8) [_]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b1 ⟨Hb1, Hcap1, -⟩
  wp_apply wp_string_to_bytes as %sl2 ⟨Hsl2, -⟩
  wp_apply wp_slice_append (V := w8) $$ [$Hb1 $Hcap1 $Hsl2] as %b2 ⟨Hb2, Hcap2, -⟩
  have he : (l ++ [W8 (sint.Z (W64 (str.length : Int)))]) ++ str = l ++ encS str := by
    simp only [encS, List.append_assoc, List.cons_append, List.nil_append]
    congr 2
    word
  rw [he]
  iapply HΦ
  iframe Hb2 Hcap2

theorem flagB_dec (p : Bool) : decide (flagB p = W8 1) = p := by
  cases p <;> simp [flagB]

theorem sliceIndexRef_slice0 (b : GoSlice) (k : w64) (i : Int) :
    sliceIndexRef w8 i (slice.slice b w8 (W64 0) k) = sliceIndexRef w8 i b := by
  simp only [slice.slice, sliceIndexRef, show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]


/-- A value the far side may answer is a bounded `Out`. -/
theorem outOk_outV (γ : CraqNames) (v : GoInterface)
    (h : (kvR (Gg := hG.goose_globalGS) γ).outOk v) :
    ∃ (u f : Bool) (w : Str8), v = outV u f w.1 := by
  simp only [RBase.outOk, kvR] at h
  rcases h with ⟨o, ho⟩ | ⟨_, ho⟩ <;> subst ho
  · rcases o with (_ | x) | _
    · exact ⟨false, false, ⟨[], by simp⟩, rfl⟩
    · exact ⟨false, true, x, rfl⟩
    · exact ⟨false, false, ⟨[], by simp⟩, rfl⟩
  · exact ⟨true, false, ⟨[], by simp⟩, rfl⟩

theorem sint_len_eq {b : GoSlice} {n : Nat} (h : n = sint.nat b.len ∧ 0 ≤ sint.Z b.len) :
    sint.Z b.len = n := by
  rw [h.1]; exact (Int.toNat_of_nonneg h.2).symm

/-- `decStr(b)` on `encS str ++ r`: `str` and the rest, `r`. -/
theorem wp_decStr (b : GoSlice) (dq : DFrac) (str : GoString) (r : List w8)
    (hs : str.length < 256) :
    {{ (b ↦*{dq} (encS str ++ r) : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.decStr)) (Val #b))
    {{ (r' : GoSlice), RET (PairV (PairV #str #r') #true); r' ↦*{dq} r }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  simp only [encS, List.cons_append, List.length_cons, List.length_append] at Hlen
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
    constructor <;> word
  wp_auto
  wp_if_destruct
  · exfalso; word
  rw [ite_eq_left h0]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (W8 str.length) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  have hn : uint.Z (W64 (uint.Z (W8 (str.length : Int)))) = str.length := by word
  wp_if_destruct
  · exfalso; word
  rw [ite_eq_left h0]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (W8 str.length) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  have hm : sint.Z (W64 1 + W64 (uint.Z (W8 (str.length : Int)))) = str.length + 1 := by word
  have hcap := Hwf.2
  have hz0 : sint.Z (W64 0) = 0 := rfl
  have hz1 : sint.Z (W64 1) = 1 := rfl
  have hbl : sint.Z b.len = ((str.length + r.length + 1 : Nat) : Int) := sint_len_eq Hlen
  push_cast at hbl
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧
      sint.Z (W64 1) ≤ sint.Z (W64 1 + W64 (uint.Z (W8 (str.length : Int)))) ∧
      sint.Z (W64 1 + W64 (uint.Z (W8 (str.length : Int)))) ≤ sint.Z b.cap by
    refine ⟨by word, by word, by omega⟩)]
  icases (ownSlice_split_all (W64 1 + W64 (uint.Z (W8 (str.length : Int)))) b dq _
    ⟨by omega, by omega⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
  icases (ownSlice_split (W64 1) b dq _ (W64 0) (W64 1 + W64 (uint.Z (W8 (str.length : Int))))
    ⟨by word, by omega, by omega⟩).1 $$ Hb1 with ⟨Hb0, Hb1⟩
  have hk : sint.nat (W64 1 + W64 (uint.Z (W8 (str.length : Int)))) = str.length + 1 := by
    rw [show sint.nat _ = (sint.Z (W64 1 + W64 (uint.Z (W8 (str.length : Int))))).toNat from rfl,
      hm]; omega
  have e1 : ((encS str ++ r).take (sint.nat (W64 1 + W64 (uint.Z (W8 (str.length : Int)))))).drop
      (sint.nat (W64 1) - sint.nat (W64 0)) = str := by
    rw [hk, show sint.nat (W64 1) - sint.nat (W64 0) = 1 from rfl]; simp [encS]
  have e2 : (encS str ++ r).drop (sint.nat (W64 1 + W64 (uint.Z (W8 (str.length : Int))))) = r := by
    rw [hk]; simp [encS]
  rw [e1, e2]
  wp_apply wp_bytes_to_string $$ Hb1 as Hb1
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 1 + W64 (uint.Z (W8 (str.length : Int)))) ∧
      sint.Z (W64 1 + W64 (uint.Z (W8 (str.length : Int)))) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap by omega)]
  wp_auto
  iapply HΦ
  iexact Hb2

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
    simp [inOk]
  · iapply HΦ
    imodintro
    ipureintro
    refine ⟨⟨.get _, ?_⟩, rfl⟩
    simp [inOk]

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
      · exact ⟨false, k, [], hi, by simp, rfl, rfl⟩
      · exact ⟨true, k, v, hi.1, hi.2, rfl, rfl⟩
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
      · exact ⟨false, k, [], hi, by simp, rfl, rfl⟩
      · exact ⟨true, k, v, hi.1, hi.2, rfl, rfl⟩
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
