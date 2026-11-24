/-
Helpers of the craq kit's proofs (`kit.go`, notes/dsv-craq.md): `wp_ServerAddrs`, `wp_ClientAddrs`,
`wp_ConfAddrs`, `wp_attempt`, `wp_digit`; the codec's helpers `wp_flag`, `wp_encStr`, `wp_decStr`,
`outOk_outV`. `KitProof.lean` proves `Codec.wp_proof` and `Gen.wp_proof` with them.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ModelDefs
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
    · exact ⟨false, false, ⟨[W8 0], by simp⟩, rfl⟩
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

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
