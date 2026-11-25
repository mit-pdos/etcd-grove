-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/CCCodecLemmas.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The part's own (raft without hand-written axioms, `notes/raft-noax-codec.md`).

# The conf change codecs: round trips and bounds (pure)

Arithmetic and bounds for the wire readers and encoders, and the loop equations
used in their Go proofs. `CCWireSound` recovers the protobuf grammar of bytes
accepted by the group scanner. `CCWireRoundtrip` proves that the decoder reads
the known and unknown fields written by all three encoders.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.CCModel

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-! ## Bits -/

theorem cc_w8_and_127 (c : w8) : uint.Z (c &&& W8 127) = uint.Z c % 128 := by
  have h : (c &&& W8 127).toNat = c.toNat % 128 := by
    rw [BitVec.toNat_and, show (W8 127).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  unfold uint.Z; rw [h]; push_cast; rfl

theorem cc_w8_or_128 (v : w64) :
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

theorem cc_w64_or_shiftl (acc : w64) (y s : Nat) (hs : s < 64) (hacc : uint.nat acc < 2 ^ s)
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

/-- Removing the first continuation byte preserves protobuf's varint shape.
The remaining value is the quotient by 128, including for non-minimal zero. -/
theorem ccIsVarint_tail (c d : w8) (tail : List w8) (h : IsVarint (c :: d :: tail)) :
    128 ≤ c.toNat ∧ IsVarint (d :: tail) ∧
      varintVal (c :: d :: tail) / 128 = varintVal (d :: tail) := by
  obtain ⟨_, hsize, hcont, hlast, hval⟩ := h
  have hc := hcont 0 (by simp)
  change 128 ≤ c.toNat at hc
  have hq : varintVal (c :: d :: tail) / 128 = varintVal (d :: tail) := by
    rw [varintVal]
    omega
  refine ⟨hc, ⟨by simp, by simp_all; omega, ?_, ?_, by omega⟩, hq⟩
  · intro n hn
    exact hcont (n + 1) (by simp_all <;> omega)
  · intro b hb
    apply hlast b
    simpa using hb

theorem cc_varintEnc_lt (n : Nat) (h : n < 128) : varintEnc n = [W8 n] := by
  rw [varintEnc]; simp [h]

theorem cc_varintEnc_ge (n : Nat) (h : ¬ n < 128) :
    varintEnc n = W8 ((n % 128 + 128 : Nat) : Int) :: varintEnc (n / 128) := by
  rw [varintEnc]; simp [h]

theorem cc_varintEnc_pos (n : Nat) : 0 < (varintEnc n).length := by
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
  · rw [cc_varintEnc_lt w h128]
    have hget : (pre ++ [W8 (w : Int)] ++ rest)[pre.length]? = some (W8 (w : Int)) := by simp
    simp only [ccVarintLoop, hget]
    have hc : uint.Z (W8 (w : Int)) = w := by word
    have hn9 : ¬ (n = 9 ∧ 1 < uint.Z (W8 (w : Int))) := by
      rintro ⟨rfl, h⟩; rw [hc] at h
      have : w < 2 := by simpa using hw
      omega
    rw [ite_eq_right hn9, ite_eq_left (by rw [hc]; omega)]
    have hm : uint.Z (W8 (w : Int) &&& W8 127) = (w : Int) := by
      rw [cc_w8_and_127, hc]; omega
    rw [hm, cc_w64_or_shiftl acc w (7 * n) (by omega) hacc hw]
    simp
  · rw [cc_varintEnc_ge w h128]
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
      rw [cc_w8_and_127, hc]; omega
    rw [hm, cc_w64_or_shiftl acc (w % 128) (7 * n) (by omega) hacc (by
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

/-- The decoder consumes every permitted varint, including a zero high group. -/
theorem ccVarintLoop_wire (wire pre rest : List w8) (n : Nat) (acc : w64)
    (valid : IsVarint wire) (hlen : n + wire.length ≤ 10)
    (hacc : uint.nat acc < 2 ^ (7*n)) (hval : varintVal wire < 2 ^ (64 - 7*n)) :
    ccVarintLoop (pre ++ wire ++ rest) (10-n) n pre.length acc (W64 (7*n : Nat)) =
      some (W64 (uint.nat acc + 2 ^ (7*n) * varintVal wire : Nat), pre.length + wire.length) := by
  induction wire generalizing n pre acc with
  | nil => obtain ⟨h, _⟩ := valid; simp at h
  | cons c cs ih =>
    have hn : n ≤ 9 := by simp at hlen; omega
    have hf : 10 - n = (9 - n) + 1 := by omega
    have hget : (pre ++ (c :: cs) ++ rest)[pre.length]? = some c := by simp
    rw [hf]
    simp only [ccVarintLoop, hget]
    have hcn : uint.Z c = (c.toNat : Int) := rfl
    have hmod : uint.Z (c &&& W8 127) = ((c.toNat % 128 : Nat) : Int) := by
      rw [cc_w8_and_127, hcn]; omega
    cases cs with
    | nil =>
      have hc : c.toNat < 128 := valid.2.2.2.1 c (by simp)
      have hv : varintVal [c] = c.toNat := by simp [varintVal, Nat.mod_eq_of_lt hc]
      have hn9 : ¬ (n = 9 ∧ 1 < uint.Z c) := by
        rintro ⟨rfl, hg⟩
        rw [hv] at hval
        have : c.toNat < 2 := hval
        omega
      rw [ite_eq_right hn9, ite_eq_left (by omega), hmod, Nat.mod_eq_of_lt hc, hv]
      rw [cc_w64_or_shiftl acc c.toNat (7*n) (by omega) hacc (hv ▸ hval)]
      rfl
    | cons d ds =>
      obtain ⟨hcont, ht, hq⟩ := ccIsVarint_tail c d ds valid
      have hn8 : n ≤ 8 := by simp at hlen; omega
      rw [ite_eq_right (by omega), ite_eq_right (by omega), hmod]
      let y := c.toNat % 128
      let w := varintVal (d :: ds)
      have hy : y < 128 := Nat.mod_lt _ (by decide)
      have hp : 2 ^ (7*(n+1)) = 2 ^ (7*n) * 128 := by
        rw [show 7*(n+1) = 7*n+7 by omega, Nat.pow_add]
      have hycap : y < 2 ^ (64-7*n) := Nat.lt_of_lt_of_le hy
        (Nat.pow_le_pow_right (by decide : 0 < 2) (show 7 ≤ 64-7*n by omega))
      rw [cc_w64_or_shiftl acc y (7*n) (by omega) hacc hycap]
      let v := uint.nat acc + 2 ^ (7*n) * y
      have hv : v < 2 ^ (7*(n+1)) := by
        have hlt := Nat.mul_le_mul_left (2 ^ (7*n)) (show y+1 ≤ 128 by omega)
        dsimp [v]; rw [Nat.mul_add, Nat.mul_one] at hlt; omega
      have hv64 : v < 2^64 := Nat.lt_of_lt_of_le hv
        (Nat.pow_le_pow_right (by decide) (show 7*(n+1) ≤ 64 by omega))
      have hword : uint.nat (W64 v) = v := by generalize v = k at hv64 ⊢; word
      have hwt : w < 2 ^ (64 - 7*(n+1)) := by
        have he : 2 ^ (64-7*n) = 2 ^ (64-7*(n+1)) * 128 := by
          rw [show 64-7*n = 64-7*(n+1)+7 by omega, Nat.pow_add]
        rw [he] at hval
        change varintVal (d :: ds) < _
        rw [← hq, Nat.div_lt_iff_lt_mul (by decide)]
        exact hval
      have hpre : pre ++ (c :: d :: ds) ++ rest = (pre ++ [c]) ++ (d :: ds) ++ rest := by simp
      have hsh : W64 (7*n : Nat) + W64 7 = W64 (7*(n+1) : Nat) := by word
      rw [hpre, hsh, show 9-n = 10-(n+1) by omega, show pre.length + 1 = (pre ++ [c]).length by simp]
      rw [ih (pre ++ [c]) (n+1) (W64 v) ht (by simp at hlen ⊢; omega) (by rw [hword]; exact hv) hwt]
      rw [hword, hp]
      have hsum : v + (2^(7*n)*128)*w = uint.nat acc + 2^(7*n)*varintVal (c::d::ds) := by
        change (uint.nat acc + 2^(7*n)*y) + (2^(7*n)*128)*w = uint.nat acc + 2^(7*n)*(y+128*w)
        simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      rw [hsum]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem ccVarintL_wire (wire pre rest : List w8) (valid : IsVarint wire) :
    ccVarintL (pre ++ wire ++ rest) pre.length =
      some (W64 (varintVal wire), pre.length + wire.length) := by
  have h := ccVarintLoop_wire wire pre rest 0 (W64 0) valid
    (by simpa using valid.2.1) (by decide) (by simpa using valid.2.2.2.2)
  simpa [ccVarintL, show uint.nat (W64 0) = 0 from rfl] using h

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

/-- Consume a tag described by protobuf-go's unknown-field invariant. The
outer decoder reads a minimal tag and the group decoder also accepts longer tags. -/
theorem ccTagL_wire (pre tag rest : List w8) (outer : Bool) (num wt : Nat)
    (valid : TagOk outer num wt tag) (hwt : wt < 8) :
    ccTagL (pre ++ tag ++ rest) pre.length (if outer then 2^29 - 1 else 2^31 - 1) =
      some (num * 8 + wt, pre.length + tag.length) := by
  obtain ⟨hlo, hhi, hbytes⟩ := valid
  have idx : (num*8 + wt) / 8 = num := by omega
  have bound : num*8 + wt < 2^64 := by cases outer <;> simp at hhi <;> omega
  have repr : uint.nat (W64 (num*8 + wt : Nat)) = num*8 + wt := by
    generalize num*8 + wt = n at bound ⊢
    word
  cases outer with
  | false =>
    obtain ⟨hv, value⟩ := hbytes
    simp only [Bool.false_eq_true, ↓reduceIte] at hhi ⊢
    have hr := ccVarintL_wire tag pre rest hv
    rw [value] at hr
    unfold ccTagL
    rw [hr]
    change (if 1 ≤ uint.nat (W64 (num*8 + wt : Nat)) / 8 ∧ uint.nat (W64 (num*8 + wt : Nat)) / 8 ≤ 2^31 - 1
      then some (uint.nat (W64 (num*8 + wt : Nat)), pre.length + tag.length) else none) = _
    rw [repr, idx, ite_eq_left ⟨hlo, by omega⟩]
  | true =>
    simp only [↓reduceIte] at hbytes hhi ⊢
    have he : ccVarint (W64 (num*8 + wt : Nat)) = tag := by rw [ccVarint, repr, hbytes]
    have hr := ccVarintL_enc pre rest (W64 (num*8 + wt : Nat))
    rw [he] at hr
    unfold ccTagL
    rw [hr]
    change (if 1 ≤ uint.nat (W64 (num*8 + wt : Nat)) / 8 ∧ uint.nat (W64 (num*8 + wt : Nat)) / 8 ≤ 2^29 - 1
      then some (uint.nat (W64 (num*8 + wt : Nat)), pre.length + tag.length) else none) = _
    rw [repr, idx, ite_eq_left ⟨hlo, by omega⟩]

/-- A length-delimited field may have a non-minimal length prefix. -/
theorem ccFieldL_wire (pre size body rest : List w8) (valid : IsVarint size)
    (lengthValue : varintVal size = body.length) :
    ccFieldL (pre ++ size ++ body ++ rest) pre.length =
      some (body, pre.length + size.length + body.length) := by
  have hbound : body.length < 2^64 := lengthValue ▸ valid.2.2.2.2
  have hv := ccVarintL_wire size pre (body ++ rest) valid
  rw [lengthValue] at hv
  have hn : uint.nat (W64 body.length) = body.length := by word
  have hz : uint.Z (W64 body.length) = (body.length : Int) := by word
  unfold ccFieldL
  rw [List.append_assoc (pre ++ size) body rest, hv]
  simp only
  rw [ite_eq_right (by simp only [List.length_append, hz]; omega), hn]
  rw [← List.length_append, List.drop_left, List.take_left, List.length_append]

theorem ccSkipScalar_wire (pre value rest : List w8) (depth num wt : Nat)
    (valid : WVal depth num wt value) (scalar : wt ≠ 3) :
    ccSkipScalar (pre ++ value ++ rest) pre.length wt =
      some (pre.length + value.length) := by
  cases valid with
  | varint d n v hv =>
    unfold ccSkipScalar
    rw [ccVarintL_wire _ pre rest hv]
    rfl
  | i64 d n v hlen =>
    simp [ccSkipScalar, hlen]
  | i32 d n v hlen =>
    simp [ccSkipScalar, hlen]
  | len d n size body hv hsize =>
    have hr := ccFieldL_wire pre size body rest hv hsize
    rw [List.append_assoc pre size body] at hr
    unfold ccSkipScalar
    rw [hr]
    simp [Nat.add_assoc]
  | group => contradiction

theorem ccEnumL_enc (pre rest : List w8) (t : w32) :
    ccEnumL (pre ++ ccEnumEnc t ++ rest) pre.length = some (t, pre.length + (ccEnumEnc t).length) := by
  unfold ccEnumL ccEnumEnc
  rw [ccVarintL_enc]
  simp only
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

/-- The encoding of the known fields of a nested change, before its unknown fields. -/
def CCSingleEnc [GooseExts] (c : ConfChangeSingleM) (bs : List w8) : Prop :=
  ∃ (ty : Option w32) (nid : Option w64), bs = ccEncodeSingle ty nid ∧
    ty.getD (W32 0) = c.Type' ∧ nid.getD (W64 0) = c.NodeId'

theorem cc_varintEnc_length_le_of_lt : ∀ (k n : Nat), n < 2 ^ (7 * (k + 1)) →
    (varintEnc n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n h
    rw [cc_varintEnc_lt n (by simpa using h)]; simp
  | succ k ih =>
    intro n h
    by_cases h128 : n < 128
    · rw [cc_varintEnc_lt n h128]; simp
    · rw [cc_varintEnc_ge n h128]
      simp only [List.length_cons]
      have h2 : n / 128 < 2 ^ (7 * (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        have : 2 ^ (7 * (k + 1 + 1)) = 2 ^ (7 * (k + 1)) * 128 := by
          rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by omega, Nat.pow_add]
        omega
      have := ih (n / 128) h2
      omega

theorem ccVarint_length_le (v : w64) : (ccVarint v).length ≤ 10 :=
  cc_varintEnc_length_le_of_lt 9 _ (by
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

/-- A successful varint read advances the index within the input. -/
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
    simp only [Option.some.injEq, Prod.mk.injEq] at h
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

theorem ccTagL_bound {b : List w8} {i maxField tag j : Nat}
    (h : ccTagL b i maxField = some (tag, j)) : i < j ∧ j ≤ b.length := by
  cases hv : ccVarintL b i with
  | none => simp [ccTagL, hv] at h
  | some p =>
    obtain ⟨v, k⟩ := p
    by_cases valid : 1 ≤ uint.nat v / 8 ∧ uint.nat v / 8 ≤ maxField
    · simp [ccTagL, hv, valid] at h
      exact h.2 ▸ ccVarintL_bound hv
    · simp [ccTagL, hv, valid] at h

theorem ccSkipScalar_bound {b : List w8} {i wt j : Nat}
    (h : ccSkipScalar b i wt = some j) : i < j ∧ j ≤ b.length := by
  unfold ccSkipScalar at h
  split at h
  · cases hv : ccVarintL b i with
    | none => simp [hv] at h
    | some p =>
      simp only [hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ ccVarintL_bound hv
  · split at h <;> simp_all <;> omega
  · cases hv : ccFieldL b i with
    | none => simp [hv] at h
    | some p =>
      simp only [hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ ccFieldL_bound hv
  · split at h <;> simp_all <;> omega
  · simp at h

theorem ccGroupLoop_bound {b : List w8} (fuel : Nat) {i j : Nat} {opened : List Nat}
    (hi : i ≤ b.length) (h : ccGroupLoop b fuel i opened = some j) :
    i ≤ j ∧ j ≤ b.length := by
  induction fuel generalizing i opened with
  | zero =>
    cases opened <;> simp_all [ccGroupLoop]
  | succ fuel ih =>
    cases opened with
    | nil => simp_all [ccGroupLoop]
    | cons num outer =>
      cases ht : ccTagL b i (2 ^ 31 - 1) with
      | none => simp [ccGroupLoop, ht] at h
      | some p =>
        obtain ⟨tag, start⟩ := p
        have hs := ccTagL_bound ht
        simp [ccGroupLoop, ht] at h
        split at h
        · split at h
          · have hh := ih hs.2 h; omega
          · contradiction
        · split at h
          · have hh := ih hs.2 h; omega
          · contradiction
        · cases hk : ccSkipScalar b start (tag % 8) with
          | none => simp [hk] at h
          | some k =>
            simp [hk] at h
            have he := ccSkipScalar_bound hk
            have hh := ih he.2 h; omega

/-- Every iteration reads a tag, so fuel beyond the remaining bytes does
not affect group decoding. -/
theorem ccGroupLoop_enough (b : List w8) (fuel extra i : Nat) (opened : List Nat)
    (enough : b.length - i ≤ fuel) :
    ccGroupLoop b (fuel + extra) i opened = ccGroupLoop b fuel i opened := by
  induction fuel generalizing i opened with
  | zero =>
    cases opened with
    | nil => simp [ccGroupLoop]
    | cons n out =>
      have hv : ccVarintL b i = none := by
        simp [ccVarintL, ccVarintLoop, List.getElem?_eq_none (show b.length ≤ i by omega)]
      cases extra <;> simp [ccGroupLoop, ccTagL, hv]
  | succ fuel ih =>
    rw [Nat.succ_add]
    cases opened with
    | nil => simp [ccGroupLoop]
    | cons num out =>
      cases ht : ccTagL b i (2^31-1) with
      | none => simp [ccGroupLoop, ht]
      | some p =>
        obtain ⟨tag, start⟩ := p
        have hstart := ccTagL_bound ht
        simp [ccGroupLoop, ht]
        split
        · split
          · exact ih _ _ (by omega)
          · rfl
        · split
          · exact ih _ _ (by omega)
          · rfl
        · cases hk : ccSkipScalar b start (tag % 8) with
          | none => simp [hk]
          | some k =>
            have he := ccSkipScalar_bound hk
            simpa [hk] using ih k (num :: out) (by omega)

theorem ccGroupLoop_eq_at (b : List w8) (fuel i : Nat) (opened : List Nat)
    (enough : b.length - i ≤ fuel) : ccGroupLoop b fuel i opened = ccGroupAt b i opened := by
  unfold ccGroupAt
  calc
    _ = ccGroupLoop b ((b.length-i) + (fuel-(b.length-i))) i opened := by
      rw [show b.length-i + (fuel-(b.length-i)) = fuel by omega]
    _ = _ := ccGroupLoop_enough b _ _ i opened (by omega)

/-- The stack and index after one group tag, with fuel reset to the remaining
input length. This is the equation of one iteration of the Go loop. -/
theorem ccGroupAt_tag {b : List w8} {i num tag start : Nat} (outer : List Nat)
    (ht : ccTagL b i (2^31-1) = some (tag, start)) :
    ccGroupAt b i (num :: outer) =
      (match tag % 8 with
       | 3 => if outer.length + 1 ≤ 10000 then ccGroupAt b start (tag/8 :: num :: outer) else none
       | 4 => if tag/8 = num then ccGroupAt b start outer else none
       | wt => (ccSkipScalar b start wt).bind fun k => ccGroupAt b k (num :: outer)) := by
  have hs := ccTagL_bound ht
  unfold ccGroupAt
  obtain ⟨fuel, hf⟩ : ∃ fuel, b.length - i = fuel + 1 := ⟨b.length - i - 1, by omega⟩
  rw [hf]
  simp [ccGroupLoop, ht]
  split
  · rename_i h3
    rw [h3]
    split
    · exact ccGroupLoop_eq_at b fuel start _ (by omega)
    · rfl
  · rename_i h4
    rw [h4]
    split
    · exact ccGroupLoop_eq_at b fuel start _ (by omega)
    · rfl
  · cases hk : ccSkipScalar b start (tag % 8) with
    | none => simp [hk]
    | some k =>
      have he := ccSkipScalar_bound hk
      simpa [hk, ccGroupAt] using ccGroupLoop_eq_at b fuel k (num :: outer) (by omega)

theorem ccGroupAt_nil (b : List w8) (i : Nat) : ccGroupAt b i [] = some i := by
  unfold ccGroupAt
  cases b.length - i <;> rfl

theorem ccGroupAt_no_tag {b : List w8} {i num : Nat} (outer : List Nat)
    (ht : ccTagL b i (2^31-1) = none) : ccGroupAt b i (num :: outer) = none := by
  unfold ccGroupAt
  cases b.length - i <;> simp [ccGroupLoop, ht]

private theorem ccGroupAt_endTag (pre etag rest : List w8) (num : Nat) (outer : List Nat)
    (valid : TagOk false num 4 etag) :
    ccGroupAt (pre ++ etag ++ rest) pre.length (num :: outer) =
      ccGroupAt (pre ++ etag ++ rest) (pre ++ etag).length outer := by
  have ht := ccTagL_wire pre etag rest false num 4 valid (by decide)
  rw [ccGroupAt_tag outer ht]
  simp [show (num*8+4)/8 = num by omega]

private theorem ccGroupAt_scalarTag (pre tag v rest : List w8) (d num wt parent : Nat)
    (outer : List Nat) (ht : TagOk false num wt tag) (hv : WVal d num wt v) (h3 : wt ≠ 3) :
    ccGroupAt (pre ++ tag ++ v ++ rest) pre.length (parent :: outer) =
      ccGroupAt (pre ++ tag ++ v ++ rest) (pre ++ tag ++ v).length (parent :: outer) := by
  have hwt : wt = 0 ∨ wt = 1 ∨ wt = 2 ∨ wt = 5 := by cases hv <;> simp_all
  have hread := ccTagL_wire pre tag (v ++ rest) false num wt ht (by omega)
  have hs := ccSkipScalar_wire (pre ++ tag) v rest d num wt hv h3
  rw [← List.append_assoc (pre ++ tag) v rest] at hread
  rw [ccGroupAt_tag outer hread]
  have hm : (num * 8 + wt) % 8 = wt := by omega
  rw [hm]
  rcases hwt with h|h|h|h <;> subst wt <;> simpa [Nat.add_assoc] using
    (congrArg (fun r => r.bind (fun k => ccGroupAt (pre ++ tag ++ v ++ rest) k (parent :: outer))) hs)

/-- Reading a sequence of well-formed fields inside an open group preserves
the stack and continues immediately after the sequence. -/
theorem ccGroupAt_fields (d : Nat) (body pre rest : List w8) (parent : Nat) (outer : List Nat)
    (valid : WFields d body) (room : outer.length + 1 + d ≤ 10001) :
    ccGroupAt (pre ++ body ++ rest) pre.length (parent :: outer) =
      ccGroupAt (pre ++ body ++ rest) (pre ++ body).length (parent :: outer) := by
  cases valid with
  | nil => simp
  | cons _ num wt tag v tail ht hv htail =>
    have htag : 0 < tag.length := ht.2.2.1.1
    have htailStep := ccGroupAt_fields d tail (pre ++ tag ++ v) rest parent outer htail room
    by_cases h3 : wt = 3
    · subst wt
      cases hv with
      | group depth _ inner etag hinner he =>
        have hread := ccTagL_wire pre tag (inner ++ etag ++ tail ++ rest) false num 3 ht (by decide)
        have hstep := ccGroupAt_tag outer (num := parent) hread
        have hroom : outer.length + 1 ≤ 10000 := by omega
        have hinnerStep := ccGroupAt_fields depth inner (pre ++ tag) (etag ++ tail ++ rest)
          num (parent :: outer) hinner (by simp; omega)
        have hend := ccGroupAt_endTag (pre ++ tag ++ inner) etag (tail ++ rest) num (parent :: outer) he
        simp [hroom, show (num*8+3)/8 = num by omega] at hstep
        simp only [List.append_assoc, List.length_append, Nat.add_assoc] at hstep hinnerStep hend htailStep ⊢
        exact hstep.trans (hinnerStep.trans (hend.trans htailStep))
    · have hstep := ccGroupAt_scalarTag pre tag v (tail ++ rest) d num wt parent outer ht hv h3
      simp only [List.append_assoc, List.length_append, Nat.add_assoc] at hstep htailStep ⊢
      exact hstep.trans htailStep
termination_by (d, body.length)
decreasing_by all_goals simp_all [List.length_append, Prod.Lex.left, Prod.Lex.right] <;> omega

/-- The production skipper accepts every value allowed by the protobuf
unknown-fields invariant, including groups nested to the decoder's limit. -/
theorem ccSkipField_wire (pre value rest : List w8) (num wt : Nat)
    (valid : WVal 10001 num wt value) :
    ccSkipField (pre ++ value ++ rest) pre.length (num * 8 + wt) = some (pre ++ value).length := by
  have hwt : wt < 8 := by cases valid <;> decide
  have hm : (num * 8 + wt) % 8 = wt := by omega
  unfold ccSkipField
  rw [hm]
  split
  · rename_i h; subst wt
    cases valid with
    | group _ _ body etag hv he =>
      have hbody := ccGroupAt_fields 10000 body pre (etag ++ rest) num [] hv (by decide)
      have hend := ccGroupAt_endTag (pre ++ body) etag rest num [] he
      simp only [List.append_assoc, List.length_append, Nat.add_assoc, ccGroupAt_nil] at hbody hend ⊢
      simpa [show (num*8+3)/8 = num by omega] using hbody.trans hend
  · simpa using ccSkipScalar_wire pre value rest 10001 num wt valid (by assumption)

theorem ccSkipField_bound {b : List w8} {i tag j : Nat} (hi : i ≤ b.length)
    (h : ccSkipField b i tag = some j) : i ≤ j ∧ j ≤ b.length := by
  unfold ccSkipField at h
  split at h
  · exact ccGroupLoop_bound _ hi h
  · obtain ⟨lo, hlen⟩ := ccSkipScalar_bound h
    exact ⟨Nat.le_of_lt lo, hlen⟩

/-- A field-handler result always ends at or after its value start. An
unknown-field skip can only succeed within the input. -/
theorem ccSkipField_advance {b : List w8} {i tag j : Nat}
    (h : ccSkipField b i tag = some j) : i ≤ j := by
  by_cases hi : i ≤ b.length
  · exact (ccSkipField_bound hi h).1
  · unfold ccSkipField at h
    split at h
    · have : b.length-i = 0 := by omega
      simp [ccGroupAt, this, ccGroupLoop] at h
    · exact Nat.le_of_lt (ccSkipScalar_bound h).1

theorem ccSingleField_advance [GooseExts] (b : List w8) (tag i : Nat) (m next : ConfChangeSingleM) (j : Nat)
    (h : ccSingleField b tag i m = some (next, j)) : i ≤ j := by
  unfold ccSingleField at h
  split at h
  · cases hv : ccEnumL b i with
    | none => simp [hv] at h
    | some p =>
      simp [hv] at h
      exact h.2 ▸ Nat.le_of_lt (ccEnumL_bound hv).1
  · cases hv : ccVarintL b i with
    | none => simp [hv] at h
    | some p =>
      simp [hv] at h
      exact h.2 ▸ Nat.le_of_lt (ccVarintL_bound hv).1
  · cases hv : ccSkipField b i tag with
    | none => simp [hv] at h
    | some k =>
      simp [hv] at h
      exact h.2 ▸ ccSkipField_advance hv

theorem ccV1Field_advance [GooseExts] (b : List w8) (tag i : Nat) (m next : ConfChangeM) (j : Nat)
    (h : ccV1Field b tag i m = some (next, j)) : i ≤ j := by
  unfold ccV1Field at h
  split at h
  · cases hv : ccVarintL b i with
    | none => simp [hv] at h
    | some p =>
      simp [hv] at h
      exact h.2 ▸ Nat.le_of_lt (ccVarintL_bound hv).1
  · cases hv : ccEnumL b i with
    | none => simp [hv] at h
    | some p =>
      simp [hv] at h
      exact h.2 ▸ Nat.le_of_lt (ccEnumL_bound hv).1
  · cases hv : ccVarintL b i with
    | none => simp [hv] at h
    | some p =>
      simp [hv] at h
      exact h.2 ▸ Nat.le_of_lt (ccVarintL_bound hv).1
  · cases hv : ccFieldL b i with
    | none => simp [hv] at h
    | some p =>
      simp [hv] at h
      exact h.2 ▸ Nat.le_of_lt (ccFieldL_bound hv).1
  · cases hv : ccSkipField b i tag with
    | none => simp [hv] at h
    | some k =>
      simp [hv] at h
      exact h.2 ▸ ccSkipField_advance hv

theorem ccV2Field_advance [GooseExts] (b : List w8) (tag i : Nat) (m next : ConfChangeV2M) (j : Nat)
    (h : ccV2Field b tag i m = some (next, j)) : i ≤ j := by
  unfold ccV2Field at h
  split at h
  · cases hv : ccEnumL b i with
    | none => simp [hv] at h
    | some p =>
      simp [hv] at h
      exact h.2 ▸ Nat.le_of_lt (ccEnumL_bound hv).1
  · cases hv : ccFieldL b i with
    | none => simp [hv] at h
    | some p =>
      cases hn : ccWireSingle p.1 with
      | none => simp [hv, hn] at h
      | some single =>
        simp [hv, hn] at h
        exact h.2 ▸ Nat.le_of_lt (ccFieldL_bound hv).1
  · cases hv : ccFieldL b i with
    | none => simp [hv] at h
    | some p =>
      simp [hv] at h
      exact h.2 ▸ Nat.le_of_lt (ccFieldL_bound hv).1
  · cases hv : ccSkipField b i tag with
    | none => simp [hv] at h
    | some k =>
      simp [hv] at h
      exact h.2 ▸ ccSkipField_advance hv

/-- Align the field loop with a suffix of its input. The tag advances the
index even when the field handler only needs a non-strict bound. -/
theorem ccWireLoop_enough {α : Type} (b : List w8) (field : Nat → Nat → α → Option (α × Nat))
    (adv : ∀ tag i m next j, field tag i m = some (next, j) → i ≤ j)
    (fuel extra i : Nat) (m : α) (henough : b.length - i ≤ fuel) :
    ccWireLoop b field (fuel + extra) i m = ccWireLoop b field fuel i m := by
  induction fuel generalizing i m with
  | zero =>
    by_cases hi : i = b.length
    · cases extra <;> simp [ccWireLoop, hi]
    · have hv : ccVarintL b i = none := by
        simp [ccVarintL, ccVarintLoop, List.getElem?_eq_none (show b.length ≤ i by omega)]
      cases extra <;> simp [ccWireLoop, hi, ccTagL, hv]
  | succ fuel ih =>
    rw [Nat.succ_add]
    by_cases hi : i = b.length
    · simp [ccWireLoop, hi]
    · cases ht : ccTagL b i (2^29-1) with
      | none => simp [ccWireLoop, hi, ht]
      | some p =>
        obtain ⟨tag, start⟩ := p
        have hs := ccTagL_bound ht
        cases hnext : field tag start m with
        | none => simp [ccWireLoop, hi, ht, hnext]
        | some q =>
          obtain ⟨next, j⟩ := q
          have hj := adv _ _ _ _ _ hnext
          simpa [ccWireLoop, hi, ht, hnext] using ih j next (by omega)

theorem ccWireAt_end {α : Type} (b : List w8)
    (field : Nat → Nat → α → Option (α × Nat)) (m : α) :
    ccWireAt b field b.length m = some m := by simp [ccWireAt, ccWireLoop]

/-- Feeding a complete field gives the same result as starting at its end
with the updated message. -/
theorem ccWireAt_step {α : Type} {b : List w8} {field : Nat → Nat → α → Option (α × Nat)}
    (adv : ∀ tag i m next j, field tag i m = some (next, j) → i ≤ j)
    {i tag start j : Nat} {m next : α}
    (ht : ccTagL b i (2^29-1) = some (tag, start)) (hv : field tag start m = some (next, j)) :
    ccWireAt b field i m = ccWireAt b field j next := by
  have hs := ccTagL_bound ht
  have hj := adv tag start m next j hv
  have hi : i ≠ b.length := by omega
  obtain ⟨fuel, hf⟩ : ∃ fuel, b.length - i = fuel + 1 := ⟨b.length - i - 1, by omega⟩
  unfold ccWireAt
  rw [hf]
  simp [ccWireLoop, hi, ht, hv]
  have e := ccWireLoop_enough b field adv (b.length-j) (fuel-(b.length-j)) j next (by omega)
  rwa [show b.length-j + (fuel-(b.length-j)) = fuel by omega] at e

/-- A failed tag read or a failed field read at a live iteration rejects the message. -/
theorem ccWireAt_no_tag {α : Type} {b : List w8} {i : Nat}
    (field : Nat → Nat → α → Option (α × Nat)) (m : α) (hi : i < b.length)
    (ht : ccTagL b i (2^29-1) = none) : ccWireAt b field i m = none := by
  obtain ⟨fuel, hf⟩ : ∃ f, b.length-i = f+1 := ⟨b.length-i-1, by omega⟩
  simp [ccWireAt, hf, ccWireLoop, Nat.ne_of_lt hi, ht]

theorem ccWireAt_bad_field {α : Type} {b : List w8} {i tag k : Nat}
    {field : Nat → Nat → α → Option (α × Nat)} (m : α)
    (ht : ccTagL b i (2^29-1) = some (tag,k)) (hv : field tag k m = none) :
    ccWireAt b field i m = none := by
  have hj := ccTagL_bound ht
  obtain ⟨fuel, hf⟩ : ∃ f, b.length-i = f+1 := ⟨b.length-i-1, by omega⟩
  simp [ccWireAt, hf, ccWireLoop, show i ≠ b.length by omega, ht, hv]

/-- A decoder preserves its getters when all remaining fields are routed to
the unknown-field buffer. The outer tags are canonical and group bodies are verbatim. -/
theorem ccWireAt_unknowns {α : Type} (schema : FieldSchema)
    (field : List w8 → Nat → Nat → α → Option (α × Nat))
    (adv : ∀ b tag i m next j, field b tag i m = some (next, j) → i ≤ j)
    (skip : ∀ b num wt i j (m : α), wt < 8 → Routed schema num wt →
      ccSkipField b i (num*8 + wt) = some j → field b (num*8 + wt) i m = some (m, j))
    (pre unknown : List w8) (m : α) (wire : ufWire schema unknown) :
    ccWireAt (pre ++ unknown) (field (pre ++ unknown)) pre.length m = some m := by
  induction wire generalizing pre with
  | nil => simpa using ccWireAt_end pre (field pre) m
  | cons num wt tag v tail ht hv hr _ ih =>
    have hwt : wt < 8 := by cases hv <;> decide
    have htag := ccTagL_wire pre tag (v ++ tail) true num wt ht hwt
    have hval := ccSkipField_wire (pre ++ tag) v tail num wt hv
    have hfield := skip _ num wt _ _ m hwt hr hval
    simp only [List.append_assoc, List.length_append, Nat.add_assoc] at htag hfield
    have hstep := ccWireAt_step (adv _) htag hfield
    have htail := ih (pre ++ tag ++ v)
    simp only [List.append_assoc, List.length_append, Nat.add_assoc] at htail ⊢
    exact hstep.trans htail

end EtcdGrove
end Perennial
