/-
The proofs of the EPaxos kit's codec and input generator (`model.go`'s `Codec()`, kit.go's `Gen`;
notes/dsv-epaxos.md): `Codec.wp_proof` (remote's `codecOk` of `epR γ`: kit.go's `putU64`/`getU64`
as remote's, the `In`'s 17-byte header, `Out`'s flag byte), `Gen.wp_proof` (`Gen`'s inputs are
`EIn`s: keys below `NKeys`, values `"v<c><d>"`, scans of `ScanN`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ModelDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64
public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote
  github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Assumptions]
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

set_option goose.wp.extras true

open encoding.binary in
/-- `u64Le x`'s byte `i` is `byte(x >> (8*i))`. -/
theorem u64Le_getElem (x i : w64) (hi : uint.nat i < 8) :
    (u64Le x)[uint.nat i]? = some (W8 (uint.Z (x >>> (W64 8 * i)))) := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, n < 8 ∧ i = W64 n := ⟨uint.nat i, hi, by word⟩
  have hn' : uint.nat (W64 n : w64) = n := by word
  rw [hn', u64Le_8]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals first | rfl | omega

/-- Storing the next byte of `l1` over `l2`. -/
theorem take_drop_set {l1 l2 : List w8} {n : Nat} {a : w8} (h1 : l1[n]? = some a)
    (h2 : n < l2.length) :
    (l1.take n ++ l2.drop n).set n a = l1.take (n + 1) ++ l2.drop (n + 1) := by
  have hn : n < l1.length := by
    rcases Nat.lt_or_ge n l1.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at h1; cases h1
  have ht : (l1.take n).length = n := by simp; omega
  rw [List.set_append, ite_eq_right (by omega), ht, Nat.sub_self, List.take_add_one, h1]
  rw [List.drop_eq_getElem_cons h2, List.set_cons_zero]
  simp

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
/-- One more byte of the little-endian decoding: `x | uint64(v) << (8*i)`. -/
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

open encoding.binary in
theorem wp_putU64 (b : GoSlice) (vs : List w8) (x : w64) (Hvs : vs.length = 8) :
    {{ (b ↦* vs : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.putU64)) (Val #b)) (Val #x))
    {{ RET #(); b ↦* (u64Le x ++ vs.drop 8) }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "Hb" ∷ b ↦* ((u64Le x).take (uint.nat i) ++ vs.drop (uint.nat i)) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i Hb]
  · iexists W64 0
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hi8 : uint.nat i < 8 := by word
    have hs : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := by word
    rw [ite_eq_left hs]
    wp_apply wp_store_slice_index b (sint.Z i) _ (W8 (uint.Z (x >>> (W64 8 * i)))) $$ [Hb] as Hb
    · iframe Hb; ipureintro; simp only [List.length_append, List.length_take, List.length_drop,
        u64Le_length]; word
    wp_for_post
    iframe
    iexists i + W64 1
    have hsn : (sint.Z i).toNat = uint.nat i := by word
    rw [hsn, take_drop_set (u64Le_getElem x i hi8) (by word),
      show uint.nat (i + W64 1) = uint.nat i + 1 by word]
    iframe
    ipureintro; word
  · have hi8 : uint.nat i = 8 := by word
    rw [hi8, List.take_of_length_le (by simp [u64Le_length])]
    wp_end


open encoding.binary in
theorem wp_getU64 (b : GoSlice) (dq : DFrac) (bs rem : List w8) (Hbs : bs.length = 8) :
    {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
      (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.getU64)) (Val #b))
    {{ RET #(leToU64 bs); b ↦*{dq} (bs ++ rem) }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "x" ∷ x_ptr ↦ leToU64 (bs.take (uint.nat i)) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i x]
  · iexists W64 0
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hi8 : uint.nat i < 8 := by word
    have hbl : (bs ++ rem).length = 8 + rem.length := by simp [Hbs]
    have hs : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := by word
    rw [ite_eq_left hs]
    have hsn : (sint.Z i).toNat = uint.nat i := by word
    obtain ⟨v, hv⟩ : ∃ v, bs[uint.nat i]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index b (sint.Z i) _ dq v (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rw [hsn, List.getElem?_append_left (by omega)]; exact hv
    wp_for_post
    iframe
    iexists i + W64 1
    rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, leToU64_take_succ bs i v hi8 hv]
    iframe
    ipureintro; word
  · have hi8 : uint.nat i = 8 := by word
    rw [hi8, List.take_of_length_le (by omega)]
    wp_end


theorem wp_digit (n : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.digit)) (Val #n))
    {{ (s : GoString), RET #s; ⌜s.length = 1⌝ }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z (W64 48 + n % W64 10))]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_bytes_to_string $$ [Hsl] as Hsl
  · iexact Hsl
  iapply HΦ
  ipureintro; rfl

theorem Gen.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG)) :
    Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec EtcdGrove.lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_apply wp_RandomUint64 as %n -
  have hk : uint.nat (n / W64 2 % W64 2) < 2 := by word
  wp_if_destruct
  · wp_apply wp_digit as %d1 %hd1
    wp_apply wp_digit as %d2 %hd2
    iapply HΦ
    imodintro
    ipureintro
    refine ⟨⟨.put (n / W64 2 % W64 2) ([118#8] ++ d1 ++ d2), ?_⟩, rfl⟩
    simp only [inPre, List.length_append, List.length_cons, List.length_nil, hd1, hd2]
    refine ⟨by word, by simp, by omega⟩
  wp_if_destruct
  · iapply HΦ
    imodintro
    ipureintro
    exact ⟨⟨.get (n / W64 2 % W64 2), by simp only [inPre]; word⟩, rfl⟩
  iapply HΦ
  imodintro
  ipureintro
  exact ⟨⟨.scan (n / W64 2 % W64 2) (W64 1), by simp only [inPre]; refine ⟨by word, by decide⟩⟩, rfl⟩

theorem not_lt17 (b : GoSlice) (n : Nat) (h : sint.Z b.len = 17 + n) :
    ¬ sint.Z b.len < sint.Z (W64 17) := by
  have : sint.Z (W64 17) = 17 := by word
  omega

theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro γ
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk epR
  simp only
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' - HΦ'
    unfold ivE
    have hV : (inE i).V'.length < 2 ^ 15 := by
      obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i <;> simp only [inE, inOf, inPre] at hi ⊢ <;> first | omega | simp
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
    wp_apply (wp_slice_make3 (V := w8) (W64 17) (W64 17 + W64 (inE i).V'.length) (by word))
      as %b ⟨Hb, Hcap, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    rw [ite_eq_left h0]
    wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (inE i).Op' $$ [Hb] as Hb
    · iframe Hb; ipureintro; simp
    have hlen17 : b.len = W64 17 := by
      have := Hbl.1; simp only [List.length_replicate] at this; word
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hcap : 17 ≤ sint.Z b.cap := by
      have := Hwf.2; rw [hlen17] at this; exact this
    rw [show (List.replicate 17 (zero_val w8)).set 0 (inE i).Op' =
      (inE i).Op' :: (List.replicate 8 (W8 0) ++ List.replicate 8 (W8 0)) from rfl]
    have e1 := ownSlice_split_all (GF := GF) (V := w8) (W64 1) b (DFrac.own 1)
      ((inE i).Op' :: (List.replicate 8 (W8 0) ++ List.replicate 8 (W8 0))) ⟨by word, by word⟩
    rw [hlen17, show sint.nat (W64 1) = 1 from rfl] at e1
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at e1
    icases e1.1 $$ Hb with ⟨H0, H1⟩
    have e2 := ownSlice_split (GF := GF) (V := w8) (W64 9) b (DFrac.own 1)
      (List.replicate 8 (W8 0) ++ List.replicate 8 (W8 0)) (W64 1) (W64 17) ⟨by word, by word, by word⟩
    rw [show sint.nat (W64 9) - sint.nat (W64 1) = 8 from rfl,
      List.take_left' (by simp), List.drop_left' (by simp)] at e2
    icases e2.1 $$ H1 with ⟨H1, H2⟩
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (W64 9) ∧
      sint.Z (W64 9) ≤ sint.Z b.cap from ⟨by word, by word, by word⟩)]
    wp_auto
    wp_apply wp_putU64 (slice.slice b w8 (W64 1) (W64 9)) (List.replicate 8 (W8 0)) (inE i).K'
      (by simp) $$ [$H1] as H1
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 9) ∧ sint.Z (W64 9) ≤ sint.Z (W64 17) ∧
      sint.Z (W64 17) ≤ sint.Z b.cap from ⟨by word, by word, by word⟩)]
    wp_auto
    wp_apply wp_putU64 (slice.slice b w8 (W64 9) (W64 17)) (List.replicate 8 (W8 0)) (inE i).N'
      (by simp) $$ [$H2] as H2
    simp only [List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil]
    ihave H12 := ownSlice_combine (V := w8) (W64 9) b (DFrac.own 1) (u64Le (inE i).K')
      (u64Le (inE i).N') (W64 1) (W64 17) ⟨by simp [u64Le_length]; rfl, by word, by word, by word⟩
      $$ H1 H2
    ihave Hb := ownSlice_combine (V := w8) (W64 1) b (DFrac.own 1) [(inE i).Op']
      (u64Le (inE i).K' ++ u64Le (inE i).N') (W64 0) (W64 17) ⟨rfl, by word, by word, by word⟩
      $$ H0 H12
    have e3 := ownSlice_trivial_slice (GF := GF) (V := w8) b (DFrac.own 1)
      ([(inE i).Op'] ++ (u64Le (inE i).K' ++ u64Le (inE i).N'))
    rw [hlen17] at e3
    icases e3.2 $$ Hb with Hb
    wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
    iapply HΦ'
    have e : encInB (inE i) =
        [(inE i).Op'] ++ (u64Le (inE i).K' ++ u64Le (inE i).N') ++ (inE i).V' := by simp [encInB]
    rw [e]
    iexact Hb'
  isplitr
  · -- DecIn
    iintro %i %b %dq
    simp only [encInB, List.append_assoc]
    iintro !> %Φ' Hb HΦ'
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hl : ((inE i).Op' :: (u64Le (inE i).K' ++ (u64Le (inE i).N' ++ (inE i).V'))).length =
        17 + (inE i).V'.length := by
      simp [u64Le_length]; omega
    have hbl : sint.Z b.len = 17 + (inE i).V'.length := by
      have h1 := Hlen.1; rw [hl] at h1
      have h2 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := by have := Hlen.2; word
      omega
    have h17 : ¬ sint.Z b.len < sint.Z (W64 17) := not_lt17 b _ hbl
    wp_auto
    rw [decide_eq_false h17]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := ⟨by word, by rw [hbl]; word⟩
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (inE i).Op' (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · iapply HΦ'
      ipureintro; nofun
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (inE i).Op' (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    have hlenw : b.len = W64 (17 + (inE i).V'.length) := by
      have := Hlen.1; rw [hl] at this; word
    have e1 := ownSlice_split_all (GF := GF) (V := w8) (W64 1) b dq
      ((inE i).Op' :: (u64Le (inE i).K' ++ (u64Le (inE i).N' ++ (inE i).V')))
      ⟨by word, by rw [hbl]; word⟩
    rw [show sint.nat (W64 1) = 1 from rfl] at e1
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero] at e1
    icases e1.1 $$ Hb with ⟨H0, H1⟩
    have e2 := ownSlice_split (GF := GF) (V := w8) (W64 9) b dq
      (u64Le (inE i).K' ++ (u64Le (inE i).N' ++ (inE i).V')) (W64 1) b.len
      ⟨by word, by word, by rw [hbl]; word⟩
    rw [show sint.nat (W64 9) - sint.nat (W64 1) = 8 from rfl,
      List.take_left' (by simp [u64Le_length]), List.drop_left' (by simp [u64Le_length])] at e2
    icases e2.1 $$ H1 with ⟨H1, H2⟩
    have e3 := ownSlice_split (GF := GF) (V := w8) (W64 17) b dq
      (u64Le (inE i).N' ++ (inE i).V') (W64 9) b.len
      ⟨by word, by word, by rw [hbl]; word⟩
    rw [show sint.nat (W64 17) - sint.nat (W64 9) = 8 from rfl,
      List.take_left' (by simp [u64Le_length]), List.drop_left' (by simp [u64Le_length])] at e3
    icases e3.1 $$ H2 with ⟨H2, H3⟩
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (W64 9) ∧
      sint.Z (W64 9) ≤ sint.Z b.cap from ⟨by word, by word, by rw [hbl] at Hwf; word⟩)]
    wp_apply wp_getU64 (slice.slice b w8 (W64 1) (W64 9)) dq (u64Le (inE i).K') []
      (by simp [u64Le_length]) $$ [H1] as H1
    · rw [List.append_nil]; iexact H1
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 9) ∧ sint.Z (W64 9) ≤ sint.Z (W64 17) ∧
      sint.Z (W64 17) ≤ sint.Z b.cap from ⟨by word, by word, by rw [hbl] at Hwf; word⟩)]
    wp_apply wp_getU64 (slice.slice b w8 (W64 9) (W64 17)) dq (u64Le (inE i).N') []
      (by simp [u64Le_length]) $$ [H2] as H2
    · rw [List.append_nil]; iexact H2
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 17) ∧ sint.Z (W64 17) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by word, by rw [hbl]; word, Hwf.2⟩)]
    wp_apply wp_bytes_to_string $$ [H3] as H3
    · iexact H3
    iapply HΦ'
    ipureintro
    intro _
    simp only [u64Le_to_word, ivE, inV]
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨u, w, rfl⟩ : ∃ (u : Bool) (w : BStr), v = outV u w.1 := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, h⟩
      · exact ⟨_, bEmpty, h⟩
    iintro !> %Φ' - HΦ'
    rw [encOutV_outV]
    have hw := w.2
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
    wp_apply (wp_slice_make3 (V := w8) (W64 1) (W64 1 + W64 w.1.length) (by word))
      as %b ⟨Hb, Hcap, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    cases u
    · wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encOutB, Bool.false_eq_true, ↓reduceIte]
      rw [show List.replicate 1 (zero_val w8) ++ w.val = W8 0 :: w.val from rfl]
      iexact Hb'
    · wp_auto
      rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encOutB, ↓reduceIte]
      rw [show (List.replicate 1 (zero_val w8)).set 0 (W8 1) ++ w.val = W8 1 :: w.val from rfl]
      iexact Hb'
  isplitr
  · -- DecOut
    iintro %v %b %dq %Hv
    obtain ⟨u, w, rfl⟩ : ∃ (u : Bool) (w : BStr), v = outV u w.1 := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, h⟩
      · exact ⟨_, bEmpty, h⟩
    iintro !> %Φ' Hb HΦ'
    rw [encOutV_outV]
    simp only [encOutB]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hw := w.2
    have hb1 : 1 ≤ sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_cons] at h1
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg h2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      constructor <;> word
    wp_auto
    wp_if_destruct
    · exfalso; word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hif <;> word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by word, by word, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 1) b dq _ ⟨by word, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
    rw [show sint.nat (W64 1) = 1 from rfl, List.drop_one, List.tail_cons]
    wp_apply wp_bytes_to_string $$ [Hb2] as Hb2
    · iexact Hb2
    iapply HΦ'
    ipureintro
    intro _
    cases u <;> rfl
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    unfold ivE
    wp_auto
    have e : decide ((inE i).Op' = W8 0) = epB.isWrite i := by
      obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i <;> simp [inE, inOf, epB, isPut]
    rw [e]
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
    wp_auto
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
