/-
`Codec()` (`model.go`) meets remote's `codecOk` of the kit's store `qR γ` (`Kit.lean`): the byte
helpers `flag`, `appendStr` (a string's length, 8 bytes little-endian, then its bytes) and `takeStr`
(its inverse), `EncIn`/`DecIn`, `EncOut`/`DecOut`, and the closures `Codec()` returns.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.Kit
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

open encoding.binary in
/-- `u64Le x`'s byte `i` is `byte(x >> (8*i))` (remote's `putU64.lean`'s lemma). -/
theorem u64Le_getElem' (x i : w64) (hi : uint.nat i < 8) :
    (u64Le x)[uint.nat i]? = some (W8 (uint.Z (x >>> (W64 8 * i)))) := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, n < 8 ∧ i = W64 n := ⟨uint.nat i, hi, by word⟩
  have hn' : uint.nat (W64 n : w64) = n := by word
  rw [hn', u64Le_8]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals first | rfl | omega

theorem u64Le_take_succ (x i : w64) (hi : uint.nat i < 8) :
    (u64Le x).take (uint.nat i + 1) =
      (u64Le x).take (uint.nat i) ++ [W8 (uint.Z (x >>> (W64 8 * i)))] := by
  rw [List.take_add_one, u64Le_getElem' x i hi]
  rfl

theorem combine_append_single (l : List w8) (v : w8) :
    LittleEndian.combine (l ++ [v]) = LittleEndian.combine l + v.toNat * 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp [LittleEndian.combine]
  | cons a l ih =>
    simp only [List.cons_append, LittleEndian.combine, ih, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 * l.length + 8 by omega, Nat.pow_add, Nat.mul_add,
      Nat.add_assoc]
    congr 2
    rw [Nat.mul_comm 256, Nat.mul_assoc]

open encoding.binary in
/-- One more byte of the little-endian decoding: `x | uint64(v) << (8*i)` (remote's
`getU64.lean`'s lemma). -/
theorem leToU64_take_succ (bs : List w8) (i : w64) (v : w8) (hi : uint.nat i < 8)
    (hv : bs[uint.nat i]? = some v) :
    leToU64 (bs.take (uint.nat i + 1)) =
      leToU64 (bs.take (uint.nat i)) ||| (W64 (uint.Z v) <<< (W64 8 * i)) := by
  have hl : (bs.take (uint.nat i)).length = uint.nat i := by
    have : uint.nat i < bs.length := by
      rcases Nat.lt_or_ge (uint.nat i) bs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hv; cases hv
    simp; omega
  have hc := combine_bound (bs.take (uint.nat i))
  rw [hl] at hc
  have hlt : 2 ^ (8 * uint.nat i) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
  have hv8 := v.isLt
  rw [List.take_add_one, hv, Option.toList_some, leToU64, leToU64Def, leToU64, leToU64Def,
    combine_append_single, hl]
  have hsh : (W64 8 * i).toNat = 8 * uint.nat i := by word
  have hw : (W64 (uint.Z v) : w64) = v.setWidth 64 := by
    simp only [W64, uint.Z, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.shiftLeft_eq', hsh,
    toNat_or_shl _ v (8 * uint.nat i) (by rw [BitVec.toNat_ofNat]; omega) (by omega)]
  simp only [BitVec.toNat_ofNat]
  have : (v.toNat + 1) * 2 ^ (8 * uint.nat i) ≤ 256 * 2 ^ (8 * uint.nat i) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : raxos.examples.quepaxanet.Assumptions]

theorem encOutV_outV (u f : Bool) (w : GoString) (h : (encOutB u f w).length < 2 ^ 63) :
    encOutV (outV (Out.mk u f w)) = encOutB u f w := by
  have hx : ∃ p : Bool × Bool × GoString, outV (Out.mk u f w) = outV (Out.mk p.1 p.2.1 p.2.2) ∧
      (encOutB p.1 p.2.1 p.2.2).length < 2 ^ 63 := ⟨(u, f, w), rfl, h⟩
  rw [encOutV, dif_pos hx]
  have := (Classical.choose_spec hx).1
  have e := outV_inj this
  simp only [Out.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  rw [← e1, ← e2, ← e3]

end dec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

theorem wp_flag (x : Bool) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.flag)) (Val #x))
    {{ RET #(flagB x); True }} := by
  wp_start
  wp_auto
  cases x
  · wp_auto
    simp only [flagB, Bool.false_eq_true, ↓reduceIte]
    iapply HΦ; itrivial
  · wp_auto
    simp only [flagB, ↓reduceIte]
    iapply HΦ; itrivial

theorem wp_appendStr (b : GoSlice) (vs : List w8) (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ b ↦* vs ∗ ownSliceCap w8 b (DFrac.own 1) }}
      (App (App (Val (@! raxos.examples.quepaxanet.appendStr)) (Val #b)) (Val #s))
    {{ (b' : GoSlice), RET #b'; b' ↦* (vs ++ strB s) ∗ ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  ihave HI : (∃ (i : w64) (b' : GoSlice), "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ b' ∗
      "Hb" ∷ b' ↦* (vs ++ (u64Le (W64 s.length)).take (uint.nat i)) ∗
      "Hcap" ∷ ownSliceCap w8 b' (DFrac.own 1) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i b Hb Hcap]
  · iexists W64 0, b
    rw [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hi8 : uint.nat i < 8 := by revert Hif; simp
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hlit] as %b2 ⟨Hb2, Hcap2, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, b2
    rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, u64Le_take_succ _ i hi8,
      ← List.append_assoc]
    iframe
    ipureintro; word
  · have hi8 : uint.nat i = 8 := by
      have : ¬ uint.nat i < 8 := by revert Hif; simp
      omega
    rw [hi8, List.take_of_length_le (by simp [u64Le_length])]
    wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb2, Hcap2, -⟩
    iapply HΦ
    rw [strB, ← List.append_assoc]
    iframe

/-- `takeStr` on `appendStr`'s bytes of `s` followed by `r`: `s`, the rest of the slice, `true`;
the slice is given back. -/
theorem wp_takeStr (b : GoSlice) (dq : DFrac) (s r : List w8) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ b ↦*{dq} (strB s ++ r) }}
      (App (Val (@! raxos.examples.quepaxanet.takeStr)) (Val #b))
    {{ RET (PairV (PairV #s #(slice.slice b w8 (W64 (8 + s.length)) b.len)) #true);
        b ↦*{dq} (strB s ++ r) }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  have hbl : (strB s ++ r).length = 8 + s.length + r.length := by
    simp [strB, u64Le_length]; omega
  have hbl' : sint.nat b.len = 8 + s.length + r.length := by rw [← Hlen.1, hbl]
  wp_auto
  wp_if_destruct
  · exfalso; revert Hif; word
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "n" ∷ n_ptr ↦ leToU64 ((strB s ++ r).take (uint.nat j)) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ 8⌝ : IProp GF) $$ [i n]
  · iexists W64 0
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hj8 : uint.nat j < 8 := by revert Hif; simp
    have hs : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z b.len := by word
    have hsn : (sint.Z j).toNat = uint.nat j := by word
    obtain ⟨w, hw⟩ : ∃ w, (strB s ++ r)[uint.nat j]? = some w :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    try rw [ite_eq_left hs]
    wp_apply wp_load_slice_index b (sint.Z j) _ dq w (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rw [hsn]; exact hw
    wp_for_post
    iframe
    iexists j + W64 1
    rw [show uint.nat (j + W64 1) = uint.nat j + 1 by word,
      leToU64_take_succ (strB s ++ r) j w hj8 hw]
    iframe
    ipureintro; word
  · have hj8 : uint.nat j = 8 := by
      have : ¬ uint.nat j < 8 := by revert Hif; simp
      omega
    have ht8 : (strB s ++ r).take 8 = u64Le (W64 s.length) := by
      simp [strB, List.take_append, u64Le_length]
    rw [hj8, ht8, u64Le_to_word]
    have hsl : (s.length : Int) < 2 ^ 63 := by have := Hlen.2; word
    wp_if_destruct
    · exfalso; revert Hif; word
    have he : (W64 8 + W64 (s.length : Int) : w64) = W64 (8 + (s.length : Int)) := by word
    rw [he]
    have hb1 : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z (W64 (8 + (s.length : Int))) ∧
        sint.Z (W64 (8 + (s.length : Int))) ≤ sint.Z b.len := by word
    rw [ite_eq_left ⟨hb1.1, hb1.2.1, Int.le_trans hb1.2.2 Hwf.2⟩]
    icases (ownSlice_slice (W64 8) (W64 (8 + (s.length : Int))) b dq _ hb1).1 $$ Hb
      with ⟨H1, H2, H3⟩
    have hsub : subslice (sint.nat (W64 8)) (sint.nat (W64 (8 + (s.length : Int))))
        (strB s ++ r) = s := by
      rw [show sint.nat (W64 8) = 8 from rfl,
        show sint.nat (W64 (8 + (s.length : Int))) = 8 + s.length by word]
      simp [subslice, strB, List.take_append, u64Le_length, List.drop_append]
    rw [hsub]
    wp_apply wp_bytes_to_string $$ [H2] as H2
    · iexact H2
    rw [he, ite_eq_left ⟨Int.le_trans hb1.1 hb1.2.1, hb1.2.2, Hwf.2⟩]
    wp_auto
    iapply HΦ
    iapply (ownSlice_slice (W64 8) (W64 (8 + (s.length : Int))) b dq _ hb1).2
    rw [hsub]
    iframe

theorem wp_EncIn (x : In) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.EncIn)) (Val #x))
    {{ (b : GoSlice), RET #b; b ↦* encInB (kin x) }} := by
  wp_start
  wp_auto
  wp_apply wp_flag
  wp_apply wp_slice_literal (V := w8) [_]
  isplitr
  · ipureintro; rfl
  iintro %lit ⟨Hlit, Hcap⟩
  wp_auto
  wp_apply wp_appendStr $$ [$Hlit $Hcap] as %b1 ⟨Hb1, Hcap1⟩
  wp_apply wp_appendStr $$ [$Hb1 $Hcap1] as %b2 ⟨Hb2, -⟩
  iapply HΦ
  rw [encInB, kin]
  simp only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append]
  iexact Hb2

theorem wp_DecIn (i : KIn) (b : GoSlice) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ b ↦*{dq} encInB i }}
      (App (Val (@! raxos.examples.quepaxanet.DecIn)) (Val #b))
    {{ RET (PairV #(In.mk i.put i.k i.v) #true); True }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  have hbl := encInB_length i
  have hbl' : sint.nat b.len = 17 + i.k.length + i.v.length := by rw [← Hlen.1, hbl]
  wp_auto
  wp_if_destruct
  · exfalso; revert Hif; word
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by word
  try rw [ite_eq_left h0]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (flagB i.put) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  wp_if_destruct
  · exfalso; revert Hif; cases i.put <;> simp [flagB] <;> word
  have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len := by word
  rw [ite_eq_left ⟨h1.1, h1.2, Hwf.2⟩]
  icases (ownSlice_split_all (W64 1) b dq _ h1).1 $$ Hb with ⟨Hb1, Hb2⟩
  have hd1 : (encInB i).drop (sint.nat (W64 1)) = strB i.k ++ strB i.v := rfl
  rw [hd1]
  wp_apply wp_takeStr $$ [Hb2] as Hb2
  · iexact Hb2
  ihave %HlenP := ownSlice_len _ _ _ $$ Hb2
  have hPl : (strB i.k ++ strB i.v).length = 16 + i.k.length + i.v.length := by
    simp [strB, u64Le_length]; omega
  have hk : 0 ≤ sint.Z (W64 (8 + (i.k.length : Int))) ∧
      sint.Z (W64 (8 + (i.k.length : Int))) ≤ sint.Z (slice.slice b w8 (W64 1) b.len).len := by
    have := HlenP.1; rw [hPl] at this; word
  icases (ownSlice_split_all (W64 (8 + (i.k.length : Int))) _ dq _ hk).1 $$ Hb2 with ⟨Hk1, Hk2⟩
  have hd2 : (strB i.k ++ strB i.v).drop (sint.nat (W64 (8 + (i.k.length : Int)))) =
      strB i.v ++ [] := by
    rw [show sint.nat (W64 (8 + (i.k.length : Int))) = 8 + i.k.length by word]
    simp [strB, List.drop_append, u64Le_length]
  rw [hd2]
  have hPlen : (slice.slice b w8 (W64 1) b.len).len = b.len - W64 1 := by
    simp [slice.slice]
  rw [hPlen]
  wp_apply wp_takeStr (slice.slice (slice.slice b w8 (W64 1) b.len) w8
      (W64 (8 + (i.k.length : Int))) (b.len - W64 1)) dq i.v [] $$ [Hk2] as Hk2
  · iexact Hk2
  have hbz : b.len - W64 1 - W64 (8 + (i.k.length : Int)) - W64 (8 + (i.v.length : Int)) = W64 0 := by
    word
  wp_if_destruct
  · ihave Hb2 : (slice.slice b w8 (W64 1) b.len ↦*{dq} (strB i.k ++ strB i.v) : IProp GF)
        $$ [Hk1 Hk2]
    · iapply (ownSlice_split_all (W64 (8 + (i.k.length : Int))) _ dq _ hk).2
      rw [hd2, List.append_nil, hPlen]
      iframe
    ihave Hb : (b ↦*{dq} encInB i : IProp GF) $$ [Hb1 Hb2]
    · iapply (ownSlice_split_all (W64 1) b dq _ h1).2
      rw [hd1]
      iframe
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (flagB i.put) (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_auto
    have hput : decide (flagB i.put = W8 1) = i.put := by
      cases i.put <;> decide
    rw [hput]
    iapply HΦ
    itrivial
  · exfalso; exact Hif hbz

theorem wp_EncOut (o : Out) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.EncOut)) (Val #o))
    {{ (b : GoSlice), RET #b; b ↦* encOutB o.Unknown' o.Found' o.V' }} := by
  wp_start
  wp_auto
  wp_apply wp_flag
  wp_apply wp_flag
  wp_apply wp_slice_literal (V := w8) [_, _]
  isplitr
  · ipureintro; rfl
  iintro %lit ⟨Hlit, Hcap⟩
  wp_auto
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append (V := w8) $$ [$Hlit $Hcap $Hsl] as %b2 ⟨Hb2, -, -⟩
  iapply HΦ
  rw [encOutB, show flagB o.Unknown' :: flagB o.Found' :: o.V' = [flagB o.Unknown', flagB o.Found'] ++ o.V' from rfl]
  iexact Hb2

theorem wp_DecOut (u f : Bool) (w : GoString) (b : GoSlice) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ b ↦*{dq} encOutB u f w }}
      (App (Val (@! raxos.examples.quepaxanet.DecOut)) (Val #b))
    {{ RET (PairV #(Out.mk u f w) #true); True }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  have hbl' : sint.nat b.len = 2 + w.length := by
    rw [← Hlen.1]; simp [encOutB]; omega
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by word
  have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by word
  wp_auto
  wp_if_destruct
  · exfalso; revert Hif; word
  rw [ite_eq_left h0]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (flagB u) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  wp_if_destruct
  · exfalso; revert Hif; cases u <;> simp [flagB] <;> word
  rw [ite_eq_left h1]
  wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (flagB f) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  wp_if_destruct
  · exfalso; revert Hif; cases f <;> simp [flagB] <;> word
  rw [ite_eq_left h0]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (flagB u) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  rw [ite_eq_left h1]
  wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (flagB f) (by word) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  have h2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z b.len := by word
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z b.len ∧
    sint.Z b.len ≤ sint.Z b.cap from ⟨h2.1, h2.2, Hwf.2⟩)]
  icases (ownSlice_split_all (W64 2) b dq _ h2).1 $$ Hb with ⟨Hb1, Hb2⟩
  rw [show (encOutB u f w).drop (sint.nat (W64 2)) = w from rfl]
  wp_apply wp_bytes_to_string $$ [Hb2] as Hb2
  · iexact Hb2
  have hu : decide (flagB u = W8 1) = u := by cases u <;> decide
  have hf : decide (flagB f = W8 1) = f := by cases f <;> decide
  rw [hu, hf]
  iapply HΦ
  itrivial

end proof

end raxos.examples.quepaxanet
end Perennial
