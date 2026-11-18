/-
The part's own (raft without hand-written axioms, `notes/raft-noax-codec.md`).

# The conf change codecs: round trips and bounds (pure)

For the proofs of `raftpb/noax.go`'s encoders and decoders (`CCCodec.lean`, `CCModel.lean`):

* the decoders' steps stay in the input (`ccVarintL_bound`, `ccEnumL_bound`, `ccFieldL_bound`,
  `ccOptField_bound`, `ccChangesLoop_bound`): what the Go loops' index invariants need;
* each decoder reads back what the matching encoder writes (`ccVarintL_enc`, `ccEnumL_enc`,
  `ccFieldL_enc`, then `ccDecodeV1_enc`, `ccDecodeSingle_enc`, `ccDecodeV2_enc`): what the
  encoders' specs promise (`ccDecodeV1 bs = some m`);
* the encodings' lengths against `ccLenMax`: `CCCodecLen.lean`.
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.CCModel

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-! ## Bits -/

theorem w8_and_127 (c : w8) : uint.Z (c &&& W8 127) = uint.Z c % 128 := by
  have h : (c &&& W8 127).toNat = c.toNat % 128 := by
    rw [BitVec.toNat_and, show (W8 127).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  unfold uint.Z; rw [h]; push_cast; rfl

theorem w8_or_128 (v : w64) :
    W8 (uint.Z v) ||| W8 128 = W8 ((uint.nat v % 128 + 128 : Nat) : Int) := by
  have hd : ∀ m, m < 256 → m ||| 128 = m % 128 + 128 := by decide +kernel
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  show (BitVec.ofInt 8 (uint.Z v)).toNat ||| (BitVec.ofInt 8 128).toNat = (BitVec.ofInt 8 _).toNat
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have : uint.Z v = ((uint.nat v : Nat) : Int) := by word
  rw [this]
  generalize uint.nat v = n
  have e1 : ((n : Int) % ((2 ^ 8 : Nat) : Int)).toNat = n % 256 := by omega
  have e2 : (((n % 128 + 128 : Nat) : Int) % ((2 ^ 8 : Nat) : Int)).toNat = n % 128 + 128 := by omega
  have e3 : ((128 : Int) % ((2 ^ 8 : Nat) : Int)).toNat = 128 := by decide
  rw [e1, e2, e3, hd _ (Nat.mod_lt _ (by decide))]
  omega

theorem w64_or_shiftl (acc : w64) (y s : Nat) (hs : s < 64) (hacc : uint.nat acc < 2 ^ s)
    (hy : y < 2 ^ (64 - s)) :
    acc ||| (W64 (y : Int) <<< W64 (s : Int)) = W64 ((uint.nat acc + 2 ^ s * y : Nat) : Int) := by
  have hp : 2 ^ (64 - s) * 2 ^ s = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have hp' : 2 ^ s * 2 ^ (64 - s) = 2 ^ 64 := by rw [Nat.mul_comm]; exact hp
  have hys : y * 2 ^ s < 2 ^ 64 := by
    rw [← hp]; exact Nat.mul_lt_mul_of_pos_right hy (Nat.two_pow_pos s)
  have hy64 : y < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right y (Nat.two_pow_pos s)) hys
  have hacc' : acc.toNat < 2 ^ s := hacc
  have e1 : (W64 (y : Int)).toNat = y := by
    show (BitVec.ofInt 64 y).toNat = y
    simp; omega
  have e2 : (W64 (s : Int)).toNat = s := by
    show (BitVec.ofInt 64 s).toNat = s
    simp; omega
  have hlt : acc.toNat + 2 ^ s * y < 2 ^ 64 := by
    have : acc.toNat + 2 ^ s * y < 2 ^ s * (y + 1) := by rw [Nat.mul_succ]; omega
    have h2 : 2 ^ s * (y + 1) ≤ 2 ^ s * 2 ^ (64 - s) := Nat.mul_le_mul_left _ hy
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  rw [e1, e2, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hys]
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hacc', Nat.shiftLeft_eq]
  show _ = (BitVec.ofInt 64 _).toNat
  rw [BitVec.toNat_ofInt]
  have : uint.nat acc = acc.toNat := rfl
  rw [this, Nat.mul_comm y]
  omega

/-! ## Varints -/

theorem varintEnc_lt (n : Nat) (h : n < 128) : varintEnc n = [W8 n] := by
  rw [varintEnc]; simp [h]

theorem varintEnc_ge (n : Nat) (h : ¬ n < 128) :
    varintEnc n = W8 ((n % 128 + 128 : Nat) : Int) :: varintEnc (n / 128) := by
  rw [varintEnc]; simp [h]

theorem varintEnc_pos (n : Nat) : 0 < (varintEnc n).length := by
  rw [varintEnc]; split <;> simp

/-- `consumeVarint`'s loop reads back `varintEnc`, from any iteration `n` whose accumulated value
is below `2^(7n)`. -/
theorem ccVarintLoop_enc (rest : List w8) : ∀ (w n : Nat) (pre : List w8) (acc : w64),
    n ≤ 9 → uint.nat acc < 2 ^ (7 * n) → w < 2 ^ (64 - 7 * n) → (0 < n → 0 < w) →
    ccVarintLoop (pre ++ varintEnc w ++ rest) (10 - n) n pre.length acc (W64 ((7 * n : Nat) : Int)) =
      some (W64 ((uint.nat acc + 2 ^ (7 * n) * w : Nat) : Int), pre.length + (varintEnc w).length) := by
  intro w
  induction w using Nat.strongRecOn with
  | _ w ih =>
  intro n pre acc hn hacc hw hpos
  obtain ⟨k, hk⟩ : ∃ k, 10 - n = k + 1 := ⟨9 - n, by omega⟩
  rw [hk]
  by_cases h128 : w < 128
  · rw [varintEnc_lt w h128]
    have hget : (pre ++ [W8 (w : Int)] ++ rest)[pre.length]? = some (W8 (w : Int)) := by simp
    simp only [ccVarintLoop, hget]
    have hc : uint.Z (W8 (w : Int)) = w := by word
    have hn9 : ¬ (n = 9 ∧ 1 < uint.Z (W8 (w : Int))) := by
      rintro ⟨rfl, h⟩; rw [hc] at h
      have : w < 2 := by simpa using hw
      omega
    have h0 : ¬ (0 < n ∧ W8 (w : Int) = W8 0) := by
      rintro ⟨hn0, h⟩
      have := hpos hn0
      have : uint.Z (W8 (w : Int)) = uint.Z (W8 0) := by rw [h]
      rw [hc] at this; have h00 : uint.Z (W8 0) = 0 := rfl; omega
    rw [ite_eq_right hn9, ite_eq_left (by rw [hc]; omega), ite_eq_right h0]
    have hm : uint.Z (W8 (w : Int) &&& W8 127) = (w : Int) := by
      rw [w8_and_127, hc]; omega
    rw [hm, w64_or_shiftl acc w (7 * n) (by omega) hacc hw]
    simp
  · rw [varintEnc_ge w h128]
    have hn9 : n ≠ 9 := by
      rintro rfl; have : w < 2 := by simpa using hw
      omega
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨8 - n, by omega⟩
    generalize hcdef : W8 ((w % 128 + 128 : Nat) : Int) = c
    have hget : (pre ++ c :: varintEnc (w / 128) ++ rest)[pre.length]? = some c := by simp
    simp only [ccVarintLoop, hget]
    have hc : uint.Z c = ((w % 128 + 128 : Nat) : Int) := by rw [← hcdef]; word
    rw [ite_eq_right (by rintro ⟨h, _⟩; exact hn9 h), ite_eq_right (by rw [hc]; omega)]
    have hm : uint.Z (c &&& W8 127) = ((w % 128 : Nat) : Int) := by
      rw [w8_and_127, hc]; omega
    rw [hm, w64_or_shiftl acc (w % 128) (7 * n) (by omega) hacc (by
      have : 2 ^ 7 ≤ 2 ^ (64 - 7 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      have := Nat.mod_lt w (show 128 > 0 by decide)
      omega)]
    have hpre : pre ++ c :: varintEnc (w / 128) ++ rest = (pre ++ [c]) ++ varintEnc (w / 128) ++ rest := by
      simp
    have hsh : W64 ((7 * n : Nat) : Int) + W64 7 = W64 ((7 * (n + 1) : Nat) : Int) := by word
    have hX : uint.nat acc + 2 ^ (7 * n) * (w % 128) < 2 ^ (7 * (n + 1)) := by
      have h1 : 2 ^ (7 * (n + 1)) = 2 ^ (7 * n) * 128 := by
        rw [show 7 * (n + 1) = 7 * n + 7 by omega, Nat.pow_add]
      have h2 : w % 128 < 128 := Nat.mod_lt _ (by decide)
      have h3 : 2 ^ (7 * n) * (w % 128) + 2 ^ (7 * n) ≤ 2 ^ (7 * n) * 128 := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
      omega
    have h64 : 2 ^ (7 * (n + 1)) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    have hXn : uint.nat (W64 ((uint.nat acc + 2 ^ (7 * n) * (w % 128) : Nat) : Int)) =
        uint.nat acc + 2 ^ (7 * n) * (w % 128) := by
      generalize uint.nat acc + 2 ^ (7 * n) * (w % 128) = x at hX
      word
    have hacc2 : uint.nat (W64 ((uint.nat acc + 2 ^ (7 * n) * (w % 128) : Nat) : Int)) <
        2 ^ (7 * (n + 1)) := by rw [hXn]; exact hX
    have hw2 : w / 128 < 2 ^ (64 - 7 * (n + 1)) := by
      have h1 : 2 ^ (64 - 7 * n) = 2 ^ (64 - 7 * (n + 1)) * 128 := by
        rw [show 64 - 7 * n = 64 - 7 * (n + 1) + 7 by omega, Nat.pow_add]
      rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
    have hfuel : k = 10 - (n + 1) := by omega
    rw [hpre, hsh, hfuel, show pre.length + 1 = (pre ++ [c]).length by simp]
    rw [ih (w / 128) (by omega) (n + 1) (pre ++ [c]) _ (by omega) hacc2 hw2 (fun _ => by omega)]
    rw [hXn]
    have hw : w = w % 128 + 128 * (w / 128) := (Nat.mod_add_div w 128).symm
    have hp : 2 ^ (7 * (n + 1)) = 2 ^ (7 * n) * 128 := by
      rw [show 7 * (n + 1) = 7 * n + 7 by omega, Nat.pow_add]
    have hsum : uint.nat acc + 2 ^ (7 * n) * (w % 128) + 2 ^ (7 * (n + 1)) * (w / 128) =
        uint.nat acc + 2 ^ (7 * n) * w := by
      rw [hp, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add (2 ^ (7 * n)), ← hw]
    rw [hsum]
    simp only [List.length_append, List.length_cons, List.length_nil]
    congr 2
    omega

theorem ccVarintL_enc (pre rest : List w8) (v : w64) :
    ccVarintL (pre ++ ccVarint v ++ rest) pre.length = some (v, pre.length + (ccVarint v).length) := by
  have h := ccVarintLoop_enc rest (uint.nat v) 0 pre (W64 0) (by omega) (by word) (by word)
    (fun h => absurd h (by omega))
  unfold ccVarintL ccVarint
  have e : W64 ((uint.nat (W64 0) + 2 ^ (7 * 0) * uint.nat v : Nat) : Int) = v := by
    have : uint.nat (W64 0) = 0 := rfl
    rw [this]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    exact w64_to_nat_id v
  rw [e] at h
  exact h

theorem ccEnumL_enc (pre rest : List w8) (t : w32) :
    ccEnumL (pre ++ ccEnumEnc t ++ rest) pre.length = some (t, pre.length + (ccEnumEnc t).length) := by
  unfold ccEnumL ccEnumEnc
  rw [ccVarintL_enc]
  simp only
  rw [ite_eq_right (by word)]
  congr 2
  word

theorem ccFieldL_enc (pre rest x : List w8) (hx : x.length < 2 ^ 64) :
    ccFieldL (pre ++ ccBytesEnc x ++ rest) pre.length =
      some (x, pre.length + (ccBytesEnc x).length) := by
  unfold ccFieldL ccBytesEnc
  rw [show pre ++ (ccVarint (W64 (x.length : Int)) ++ x) ++ rest =
    pre ++ ccVarint (W64 (x.length : Int)) ++ (x ++ rest) by simp, ccVarintL_enc]
  simp only
  have hl : uint.nat (W64 (x.length : Int)) = x.length := by word
  have hl' : uint.Z (W64 (x.length : Int)) = x.length := by word
  rw [ite_eq_right (by simp only [List.length_append, hl']; omega)]
  rw [hl]
  have hd : (pre ++ ccVarint (W64 (x.length : Int)) ++ (x ++ rest)).drop
      (pre.length + (ccVarint (W64 (x.length : Int))).length) = x ++ rest := by
    rw [← List.length_append]; exact List.drop_left
  rw [hd, List.take_left]
  simp only [List.length_append]
  congr 2
  omega

theorem ccOptField_none {α : Type} (b : List w8) (i : Nat) (tag : w8)
    (f : List w8 → Nat → Option (α × Nat)) (h : b[i]? ≠ some tag) :
    ccOptField b i tag f = some (none, i) := by
  unfold ccOptField; rw [ite_eq_right h]

theorem ccOptField_encOpt {α : Type} (tag : w8) (enc : α → List w8)
    (f : List w8 → Nat → Option (α × Nat)) (o : Option α) (pre rest : List w8)
    (hf : ∀ a, o = some a → ∀ pre' rest' : List w8,
      f (pre' ++ enc a ++ rest') pre'.length = some (a, pre'.length + (enc a).length))
    (hrest : rest[0]? ≠ some tag) :
    ccOptField (pre ++ ccEncOpt tag enc o ++ rest) pre.length tag f =
      some (o, pre.length + (ccEncOpt tag enc o).length) := by
  cases o with
  | none =>
    simp only [ccEncOpt, List.append_nil, List.length_nil, Nat.add_zero]
    apply ccOptField_none
    rw [List.getElem?_append_right (by simp)]; simpa using hrest
  | some a =>
    simp only [ccEncOpt]
    unfold ccOptField
    rw [ite_eq_left (by simp)]
    have := hf a rfl (pre ++ [tag]) rest
    rw [show pre ++ tag :: enc a ++ rest = pre ++ [tag] ++ enc a ++ rest by simp,
      show pre.length + 1 = (pre ++ [tag]).length by simp, this]
    simp only [Option.map_some, List.length_append, List.length_cons, List.length_nil]
    congr 2
    omega

theorem ccEncOpt_head {α : Type} (tag x : w8) (enc : α → List w8) (o : Option α) (r : List w8)
    (h1 : tag ≠ x) (h2 : r[0]? ≠ some x) : (ccEncOpt tag enc o ++ r)[0]? ≠ some x := by
  cases o with
  | none => simpa [ccEncOpt] using h2
  | some a => simp [ccEncOpt]; exact h1

/-- `MarshalConfChangeV1`'s output decodes back: the set fields' values, zero for the unset
ones. -/
theorem ccDecodeV1_enc [GooseExts] (id : Option w64) (ty : Option w32) (nid : Option w64)
    (ctx : Option (List w8)) (hctx : ∀ c, ctx = some c → c.length < 2 ^ 64) :
    ccDecodeV1 (ccEncodeV1 id ty nid ctx) =
      some ⟨ty.getD (W32 0), nid.getD (W64 0), ctx.getD [], id.getD (W64 0)⟩ := by
  unfold ccDecodeV1 ccEncodeV1
  generalize he1 : ccEncOpt (W8 8) ccVarint id = e1
  generalize he2 : ccEncOpt (W8 16) ccEnumEnc ty = e2
  generalize he3 : ccEncOpt (W8 24) ccVarint nid = e3
  generalize he4 : ccEncOpt (W8 34) ccBytesEnc ctx = e4
  have h4 : ccOptField (e1 ++ e2 ++ e3 ++ e4) (e1 ++ e2 ++ e3).length (W8 34) ccFieldL =
      some (ctx, (e1 ++ e2 ++ e3).length + e4.length) := by
    have := ccOptField_encOpt (W8 34) ccBytesEnc ccFieldL ctx (e1 ++ e2 ++ e3) []
      (fun a ha pre' rest' => ccFieldL_enc pre' rest' a (hctx a ha)) (by simp)
    rw [he4, List.append_nil] at this; exact this
  have h3 : ccOptField (e1 ++ e2 ++ e3 ++ e4) (e1 ++ e2).length (W8 24) ccVarintL =
      some (nid, (e1 ++ e2).length + e3.length) := by
    have := ccOptField_encOpt (W8 24) ccVarint ccVarintL nid (e1 ++ e2) e4
      (fun a _ pre' rest' => ccVarintL_enc pre' rest' a)
      (by rw [← he4]; simpa using ccEncOpt_head (W8 34) (W8 24) ccBytesEnc ctx [] (by decide) (by simp))
    rw [he3] at this; exact this
  have h2 : ccOptField (e1 ++ e2 ++ e3 ++ e4) e1.length (W8 16) ccEnumL =
      some (ty, e1.length + e2.length) := by
    have := ccOptField_encOpt (W8 16) ccEnumEnc ccEnumL ty e1 (e3 ++ e4)
      (fun a _ pre' rest' => ccEnumL_enc pre' rest' a)
      (by rw [← he3, ← he4]
          exact ccEncOpt_head (W8 24) (W8 16) ccVarint nid _ (by decide)
            (by simpa using ccEncOpt_head (W8 34) (W8 16) ccBytesEnc ctx [] (by decide) (by simp)))
    rw [he2, ← List.append_assoc] at this; exact this
  have h1 : ccOptField (e1 ++ e2 ++ e3 ++ e4) 0 (W8 8) ccVarintL = some (id, e1.length) := by
    have := ccOptField_encOpt (W8 8) ccVarint ccVarintL id [] (e2 ++ e3 ++ e4)
      (fun a _ pre' rest' => ccVarintL_enc pre' rest' a)
      (by rw [← he2, ← he3, ← he4, List.append_assoc]
          refine ccEncOpt_head (W8 16) (W8 8) ccEnumEnc ty _ (by decide) ?_
          refine ccEncOpt_head (W8 24) (W8 8) ccVarint nid _ (by decide) ?_
          simpa using ccEncOpt_head (W8 34) (W8 8) ccBytesEnc ctx [] (by decide) (by simp))
    rw [he1, List.nil_append, ← List.append_assoc, ← List.append_assoc] at this
    simpa using this
  simp only [h1, Option.bind_some]
  rw [show e1.length = (e1).length from rfl, h2]
  simp only [Option.bind_some]
  rw [show e1.length + e2.length = (e1 ++ e2).length by simp, h3]
  simp only [Option.bind_some]
  rw [show (e1 ++ e2).length + e3.length = (e1 ++ e2 ++ e3).length by simp only [List.length_append], h4]
  simp only [Option.bind_some]
  rw [ite_eq_left (by simp only [List.length_append])]

theorem ccDecodeSingle_enc [GooseExts] (ty : Option w32) (nid : Option w64) :
    ccDecodeSingle (ccEncodeSingle ty nid) = some ⟨ty.getD (W32 0), nid.getD (W64 0)⟩ := by
  unfold ccDecodeSingle ccEncodeSingle
  generalize he1 : ccEncOpt (W8 8) ccEnumEnc ty = e1
  generalize he2 : ccEncOpt (W8 16) ccVarint nid = e2
  have h2 : ccOptField (e1 ++ e2) e1.length (W8 16) ccVarintL = some (nid, e1.length + e2.length) := by
    have := ccOptField_encOpt (W8 16) ccVarint ccVarintL nid e1 []
      (fun a _ pre' rest' => ccVarintL_enc pre' rest' a) (by simp)
    rw [he2, List.append_nil] at this; exact this
  have h1 : ccOptField (e1 ++ e2) 0 (W8 8) ccEnumL = some (ty, e1.length) := by
    have := ccOptField_encOpt (W8 8) ccEnumEnc ccEnumL ty [] e2
      (fun a _ pre' rest' => ccEnumL_enc pre' rest' a)
      (by rw [← he2]; simpa using ccEncOpt_head (W8 16) (W8 8) ccVarint nid [] (by decide) (by simp))
    rw [he1, List.nil_append] at this
    simpa using this
  simp only [h1, Option.bind_some, h2]
  rw [ite_eq_left (by simp only [List.length_append])]

/-- `bs` is what `marshalConfChangeSingle` writes for a change holding `c`: the encoding of its set
fields, an unset one being zero in the model. -/
def CCSingleEnc [GooseExts] (c : ConfChangeSingleM) (bs : List w8) : Prop :=
  ∃ (ty : Option w32) (nid : Option w64), bs = ccEncodeSingle ty nid ∧
    ty.getD (W32 0) = c.Type' ∧ nid.getD (W64 0) = c.NodeId'

theorem ccDecodeSingle_of [GooseExts] {c : ConfChangeSingleM} {bs : List w8} (h : CCSingleEnc c bs) :
    ccDecodeSingle bs = some c := by
  obtain ⟨ty, nid, rfl, h1, h2⟩ := h
  rw [ccDecodeSingle_enc, h1, h2]

theorem varintEnc_length_le_of_lt : ∀ (k n : Nat), n < 2 ^ (7 * (k + 1)) →
    (varintEnc n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n h
    rw [varintEnc_lt n (by simpa using h)]; simp
  | succ k ih =>
    intro n h
    by_cases h128 : n < 128
    · rw [varintEnc_lt n h128]; simp
    · rw [varintEnc_ge n h128]
      simp only [List.length_cons]
      have h2 : n / 128 < 2 ^ (7 * (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        have : 2 ^ (7 * (k + 1 + 1)) = 2 ^ (7 * (k + 1)) * 128 := by
          rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by omega, Nat.pow_add]
        omega
      have := ih (n / 128) h2
      omega

theorem ccVarint_length_le (v : w64) : (ccVarint v).length ≤ 10 :=
  varintEnc_length_le_of_lt 9 _ (by
    have : uint.nat v < 2 ^ 64 := by word
    have h : (2 : Nat) ^ 64 ≤ 2 ^ (7 * (9 + 1)) := Nat.pow_le_pow_right (by decide) (by decide)
    omega)

theorem ccEncodeSingle_length_le (ty : Option w32) (nid : Option w64) :
    (ccEncodeSingle ty nid).length ≤ 22 := by
  unfold ccEncodeSingle ccEnumEnc
  cases ty <;> cases nid <;> simp only [ccEncOpt, List.length_append, List.length_cons,
    List.length_nil] <;>
    first
    | omega
    | (have := ccVarint_length_le (W64 (sint.Z ‹w32›)); omega)
    | (have := ccVarint_length_le ‹w64›; omega)
    | (have := ccVarint_length_le (W64 (sint.Z ‹w32›)); have := ccVarint_length_le ‹w64›; omega)

theorem ccEncChanges_head (encs : List (List w8)) (r : List w8) (x : w8) (h1 : W8 18 ≠ x)
    (h2 : r[0]? ≠ some x) : (ccEncChanges encs ++ r)[0]? ≠ some x := by
  cases encs with
  | nil => simpa [ccEncChanges] using h2
  | cons e es => simp [ccEncChanges]; exact h1

theorem ccEncChanges_length (encs : List (List w8)) :
    encs.length ≤ (ccEncChanges encs).length := by
  induction encs with
  | nil => simp [ccEncChanges]
  | cons e es ih => simp only [ccEncChanges, List.length_append, List.length_cons]; omega

/-- `UnmarshalConfChangeV2`'s loop reads back the changes `MarshalConfChangeV2` writes. -/
theorem ccChangesLoop_enc [GooseExts] (rest : List w8) (hrest : rest[0]? ≠ some (W8 18)) :
    ∀ (cs : List ConfChangeSingleM) (encs : List (List w8)), List.Forall₂ CCSingleEnc cs encs →
    ∀ (pre : List w8) (acc : List ConfChangeSingleM) (fuel : Nat), encs.length < fuel →
    ccChangesLoop (pre ++ ccEncChanges encs ++ rest) fuel pre.length acc =
      some (acc ++ cs, pre.length + (ccEncChanges encs).length) := by
  intro cs encs H
  induction H with
  | nil =>
    intro pre acc fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [ccChangesLoop, ccEncChanges, List.append_nil, List.length_nil, Nat.add_zero]
    rw [ite_eq_right (by rw [List.getElem?_append_right (by simp)]; simpa using hrest)]
  | @cons c e cs' encs' hce _ ih =>
    intro pre acc fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [ccEncChanges]
    unfold ccChangesLoop
    rw [ite_eq_left (by simp)]
    obtain ⟨ty, nid, rfl, -, -⟩ := id hce
    have hfl := ccFieldL_enc (pre ++ [W8 18]) (ccEncChanges encs' ++ rest) (ccEncodeSingle ty nid)
      (by have := ccEncodeSingle_length_le ty nid; omega)
    rw [show pre ++ (W8 18 :: ccBytesEnc (ccEncodeSingle ty nid) ++ ccEncChanges encs') ++ rest =
      pre ++ [W8 18] ++ ccBytesEnc (ccEncodeSingle ty nid) ++ (ccEncChanges encs' ++ rest) by simp,
      show pre.length + 1 = (pre ++ [W8 18]).length by simp, hfl]
    simp only
    rw [ccDecodeSingle_of hce]
    simp only
    have := ih (pre ++ [W8 18] ++ ccBytesEnc (ccEncodeSingle ty nid)) (acc ++ [c]) f
      (by simp at hf; omega)
    rw [show pre ++ [W8 18] ++ ccBytesEnc (ccEncodeSingle ty nid) ++ ccEncChanges encs' ++ rest =
      pre ++ [W8 18] ++ ccBytesEnc (ccEncodeSingle ty nid) ++ (ccEncChanges encs' ++ rest) by simp]
      at this
    rw [show (pre ++ [W8 18]).length + (ccBytesEnc (ccEncodeSingle ty nid)).length =
      (pre ++ [W8 18] ++ ccBytesEnc (ccEncodeSingle ty nid)).length by simp only [List.length_append],
      this]
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_cons]
    congr 2
    omega

/-- `MarshalConfChangeV2`'s output decodes back. -/
theorem ccDecodeV2_enc [GooseExts] (t : Option w32) (cs : List ConfChangeSingleM)
    (encs : List (List w8)) (H : List.Forall₂ CCSingleEnc cs encs) (ctx : Option (List w8))
    (hctx : ∀ c, ctx = some c → c.length < 2 ^ 64) :
    ccDecodeV2 (ccEncodeV2 t encs ctx) = some ⟨t.getD (W32 0), cs, ctx.getD []⟩ := by
  unfold ccDecodeV2 ccEncodeV2
  generalize he1 : ccEncOpt (W8 8) ccEnumEnc t = e1
  generalize he2 : ccEncChanges encs = e2
  generalize he3 : ccEncOpt (W8 26) ccBytesEnc ctx = e3
  have h3 : ccOptField (e1 ++ e2 ++ e3) (e1 ++ e2).length (W8 26) ccFieldL =
      some (ctx, (e1 ++ e2).length + e3.length) := by
    have := ccOptField_encOpt (W8 26) ccBytesEnc ccFieldL ctx (e1 ++ e2) []
      (fun a ha pre' rest' => ccFieldL_enc pre' rest' a (hctx a ha)) (by simp)
    rw [he3, List.append_nil] at this; exact this
  have h2 : ccChangesLoop (e1 ++ e2 ++ e3) ((e1 ++ e2 ++ e3).length + 1) e1.length [] =
      some (cs, e1.length + e2.length) := by
    have := ccChangesLoop_enc e3
      (by rw [← he3]; simpa using ccEncOpt_head (W8 26) (W8 18) ccBytesEnc ctx [] (by decide) (by simp))
      cs encs H e1 [] ((e1 ++ e2 ++ e3).length + 1)
      (by have := ccEncChanges_length encs; rw [he2] at this; simp only [List.length_append]; omega)
    rw [he2] at this; simpa using this
  have h1 : ccOptField (e1 ++ e2 ++ e3) 0 (W8 8) ccEnumL = some (t, e1.length) := by
    have := ccOptField_encOpt (W8 8) ccEnumEnc ccEnumL t [] (e2 ++ e3)
      (fun a _ pre' rest' => ccEnumL_enc pre' rest' a)
      (by rw [← he2, ← he3]
          exact ccEncChanges_head encs _ (W8 8) (by decide)
            (by simpa using ccEncOpt_head (W8 26) (W8 8) ccBytesEnc ctx [] (by decide) (by simp)))
    rw [he1, List.nil_append, ← List.append_assoc] at this
    simpa using this
  simp only [h1, Option.bind_some, h2]
  rw [show e1.length + e2.length = (e1 ++ e2).length by simp only [List.length_append], h3]
  simp only [Option.bind_some]
  rw [ite_eq_left (by simp only [List.length_append])]

/-! ## The decoders stay in the input -/

theorem ccVarintLoop_bound (b : List w8) : ∀ (fuel n i : Nat) (v s : w64) (x : w64) (j : Nat),
    ccVarintLoop b fuel n i v s = some (x, j) → i < j ∧ j ≤ b.length := by
  intro fuel
  induction fuel with
  | zero => intro n i v s x j h; simp [ccVarintLoop] at h
  | succ f ih =>
    intro n i v s x j h
    unfold ccVarintLoop at h
    cases hb : b[i]? with
    | none => rw [hb] at h; simp at h
    | some c =>
      rw [hb] at h
      have hi : i < b.length := (List.getElem?_eq_some_iff.mp hb).1
      simp only at h
      split at h
      · simp at h
      · split at h
        · split at h
          · simp at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
        · have := ih _ _ _ _ _ _ h; omega

theorem ccVarintL_bound {b : List w8} {i : Nat} {x : w64} {j : Nat} (h : ccVarintL b i = some (x, j)) :
    i < j ∧ j ≤ b.length := ccVarintLoop_bound b _ _ _ _ _ _ _ h

theorem ccEnumL_bound {b : List w8} {i : Nat} {x : w32} {j : Nat} (h : ccEnumL b i = some (x, j)) :
    i < j ∧ j ≤ b.length := by
  unfold ccEnumL at h
  split at h
  · simp at h
  · rename_i v j' hv
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ccVarintL_bound hv

theorem ccFieldL_bound {b : List w8} {i : Nat} {x : List w8} {j : Nat} (h : ccFieldL b i = some (x, j)) :
    i < j ∧ j ≤ b.length := by
  unfold ccFieldL at h
  split at h
  · simp at h
  · rename_i l j' hv
    have := ccVarintL_bound hv
    split at h
    · simp at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have : uint.Z l = (uint.nat l : Int) := by word
      omega

theorem ccOptField_bound {α : Type} {b : List w8} {i : Nat} {tag : w8}
    {f : List w8 → Nat → Option (α × Nat)}
    (hf : ∀ (i' : Nat) (x : α) (j' : Nat), f b i' = some (x, j') → i' < j' ∧ j' ≤ b.length)
    (hi : i ≤ b.length) {o : Option α} {j : Nat} (h : ccOptField b i tag f = some (o, j)) :
    i ≤ j ∧ j ≤ b.length := by
  unfold ccOptField at h
  split at h
  · cases hfb : f b (i + 1) with
    | none => rw [hfb] at h; simp at h
    | some p =>
      rw [hfb] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have := hf (i + 1) p.1 p.2 hfb; omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega

theorem ccChangesLoop_bound [GooseExts] (b : List w8) : ∀ (fuel i : Nat) (acc : List ConfChangeSingleM)
    (cs : List ConfChangeSingleM) (j : Nat), i ≤ b.length →
    ccChangesLoop b fuel i acc = some (cs, j) → i ≤ j ∧ j ≤ b.length := by
  intro fuel
  induction fuel with
  | zero => intro i acc cs j hi h; simp only [ccChangesLoop, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ f ih =>
    intro i acc cs j hi h
    unfold ccChangesLoop at h
    split at h
    · split at h
      · simp at h
      · rename_i v j' hv
        have := ccFieldL_bound hv
        split at h
        · simp at h
        · have := ih _ _ _ _ (by omega) h; omega
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega


end EtcdGrove
end Perennial
