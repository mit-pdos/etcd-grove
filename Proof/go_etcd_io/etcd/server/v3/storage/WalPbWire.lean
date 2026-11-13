/-
**The wire format of a `walpb.Record`** (W1/W6 of `notes/wal-fsext-plan.md`, §2.3, "Record bytes"):
what protobuf-go's `proto.Marshal`/`MarshalAppend` produce for a `walpb.Record`, as a transparent
Lean function of the message's wire content, and the facts about those bytes the WAL's proof uses.
Pure (no Go types): the registration of `walpb.Record` as a protobuf message type, with its trusted
facts, is in the part `LinuxFs/` (`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/PbRecord.lean`).

`server/storage/wal/walpb/record.proto` (proto2) at the fork's pin:

    message Record {
      optional int64 type  = 1;
      optional uint32 crc  = 2;
      optional bytes data  = 3;
    }

protobuf-go marshals a generated message's set fields in field-number order, then its unknown
fields verbatim (`internal/impl/encode.go`, the coder fields sorted by number); a proto2 optional
scalar is written iff its pointer is non-nil (zero included): its tag, then the value as a varint
(`int64` as its 64-bit two's complement, `uint32` as is); a `bytes` field iff its slice is non-nil
(empty included): its tag, the length as a varint, the bytes. Every number is below 16, so every
tag is one byte (`varintEnc (num * 8 + wt)`). Checked against Go by `examples/stdlib/walpb`
(`TestRecordEncoder`).

The facts:
- `recEnc_length`: the encoding's length is `recSize` (protobuf's size formula).
- `recEnc_blk` (the first wire fact of `nonissues/etcd-wal-cut-reuses-stale-tmp.md`): in the
  encoding of a record whose data, if non-empty, is itself such a block, no two zero bytes are
  adjacent and the first byte is not zero (a tag).
- `window_len_or_zeros` (the second): an 8-byte window read as a length word inside such bytes
  followed by zeros is either a length of `2^24` or more, or everything from its fourth byte on is
  zero.
-/
module

public import Proof.google_golang_org.protobuf.proto.UfWire
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecode

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

/-! ## The encoding -/

/-- A proto2 optional varint field numbered `num`: absent, or its tag and value. -/
def optVarintField (num : Nat) : Option Nat → List w8
  | none => []
  | some v => varintEnc (num * 8) ++ varintEnc v

/-- A proto2 optional `bytes` field numbered `num`: absent (a nil slice), or its tag, length and
bytes. -/
def optBytesField (num : Nat) : Option (List w8) → List w8
  | none => []
  | some d => varintEnc (num * 8 + 2) ++ varintEnc d.length ++ d

/-- **A `walpb.Record`'s wire content**: each field's presence (`Type`, `Crc` nil or a pointer to a
value; `Data` nil or not) and the unknown fields' bytes. -/
structure RecC where
  typ : Option w64
  crc : Option w32
  data : Option (List w8)
  uf : List w8
deriving DecidableEq

/-- What the getters read (`GetType()`, `GetCrc()`, `Data`): `WalRec`. -/
def RecC.model (c : RecC) : WalRec :=
  ⟨c.typ.getD 0#64, c.crc.getD 0#32, c.data.getD []⟩

/-- **The bytes protobuf-go writes for a `walpb.Record` holding `c`** (see the file header). -/
def recEnc (c : RecC) : List w8 :=
  optVarintField 1 (c.typ.map uint.nat) ++ optVarintField 2 (c.crc.map uint.nat) ++
    optBytesField 3 c.data ++ c.uf

/-- **protobuf's size of a `walpb.Record`** (`proto.Size`). -/
def recSize (c : RecC) : Nat :=
  (match c.typ with | none => 0 | some t => 1 + varintSize (uint.nat t)) +
  (match c.crc with | none => 0 | some v => 1 + varintSize (uint.nat v)) +
  (match c.data with | none => 0 | some d => 1 + varintSize d.length + d.length) +
  c.uf.length

/-- **`record.proto`'s schema** (`UfWire.lean`): `type` 1 and `crc` 2 varints, `data` 3
length-delimited. -/
def recSchema : FieldSchema := [(1, [0]), (2, [0]), (3, [2])]

/-- **The record the WAL's encoder writes for `r`** (`encode`, encoder.go:66-93): `Type` and `Crc`
always set (`encode` refuses a nil type and sets `Crc`), no unknown fields, and `Data` nil exactly
for a CRC record without data (the CRC records of `Create` and `cut`, wal.go, are built without
`Data`; every other record's data is a `Marshal` result, never nil, or the caller's metadata, which
the WAL's specs take non-nil). -/
def recOf (r : WalRec) : RecC :=
  ⟨some r.typ, some r.crc, if r.typ = crcType ∧ r.data = [] then none else some r.data, []⟩

/-- **The record bytes the WAL writes** (`WalCodec.encRec`). -/
def walRecEnc (r : WalRec) : List w8 := recEnc (recOf r)

/-! ## Size and model -/

theorem one_le_varintSize (n : Nat) : 1 ≤ varintSize n := by
  unfold varintSize
  rw [varintEnc]
  split <;> simp

/-- A one-byte tag: a field number below 16. -/
theorem varintSize_tag (n : Nat) (h : n < 128) : varintSize n = 1 := by
  unfold varintSize; rw [varintEnc, dite_eq_left h]; rfl

theorem recEnc_length (c : RecC) : (recEnc c).length = recSize c := by
  rcases c with ⟨t, k, d, u⟩
  unfold recEnc recSize
  have h1 : varintSize (1 * 8) = 1 := varintSize_tag _ (by decide)
  have h2 : varintSize (2 * 8) = 1 := varintSize_tag _ (by decide)
  have h3 : varintSize (3 * 8 + 2) = 1 := varintSize_tag _ (by decide)
  unfold varintSize at h1 h2 h3
  cases t <;> cases k <;> cases d <;>
    simp [optVarintField, optBytesField, varintSize, h1, h2, h3] <;> omega

theorem recOf_model (r : WalRec) : (recOf r).model = r := by
  rcases r with ⟨t, k, d⟩
  unfold recOf RecC.model
  by_cases h : t = crcType ∧ d = []
  · simp only [h, and_self, ite_true, Option.getD_some, Option.getD_none]
  · simp only [h, ite_false, Option.getD_some]

theorem recOf_uf (r : WalRec) : (recOf r).uf = [] := rfl

theorem walRecEnc_ne (r : WalRec) : walRecEnc r ≠ [] := by
  unfold walRecEnc recEnc recOf optVarintField
  simp only [Option.map_some, List.append_assoc, ne_eq, List.append_eq_nil_iff, not_and]
  intro h
  have : varintEnc (1 * 8) = [W8 8] := by rw [varintEnc, dite_eq_left (by decide)]; rfl
  rw [this] at h
  simp at h

/-! ## No two adjacent zero bytes (the stale-`N.tmp` argument) -/

/-- No two adjacent bytes of `xs` are both zero. -/
def NoAdjZero : List w8 → Prop
  | a :: b :: rest => ¬(a = 0#8 ∧ b = 0#8) ∧ NoAdjZero (b :: rest)
  | _ => True

/-- **A block**: non-empty, starting with a non-zero byte, with no two adjacent zeros. Blocks
concatenate (`Blk.append`): a protobuf field (a tag, never zero, then its value) is one. -/
def Blk (xs : List w8) : Prop := NoAdjZero xs ∧ ∃ x t, xs = x :: t ∧ x ≠ 0#8

theorem noAdjZero_cons_cons (a b : w8) (t : List w8) :
    NoAdjZero (a :: b :: t) ↔ ¬(a = 0#8 ∧ b = 0#8) ∧ NoAdjZero (b :: t) := Iff.rfl

theorem noAdjZero_tail {a : w8} {t : List w8} (h : NoAdjZero (a :: t)) : NoAdjZero t := by
  cases t with
  | nil => trivial
  | cons b t => exact h.2

/-- Appending a list starting with a non-zero byte keeps no-adjacent-zeros. -/
theorem noAdjZero_append_head (a b : List w8) (ha : NoAdjZero a) (hb : NoAdjZero b)
    (h : ∀ x t, b = x :: t → x ≠ 0#8) : NoAdjZero (a ++ b) := by
  induction a with
  | nil => exact hb
  | cons x a ih =>
    cases a with
    | nil =>
      cases b with
      | nil => trivial
      | cons y t => exact ⟨fun hc => h y t rfl hc.2, hb⟩
    | cons y a' => exact ⟨ha.1, ih ha.2⟩

/-- Appending to a list whose last byte is not zero keeps no-adjacent-zeros. -/
theorem noAdjZero_append_last (a b : List w8) (ha : NoAdjZero a) (hb : NoAdjZero b)
    (h : ∀ x, a.getLast? = some x → x ≠ 0#8) : NoAdjZero (a ++ b) := by
  induction a with
  | nil => exact hb
  | cons x a ih =>
    cases a with
    | nil =>
      cases b with
      | nil => trivial
      | cons y t => exact ⟨fun hc => h x rfl hc.1, hb⟩
    | cons y a' =>
      refine ⟨ha.1, ih ha.2 ?_⟩
      intro z hz
      apply h z
      simpa [List.getLast?_cons_cons] using hz

theorem Blk.append {a b : List w8} (ha : Blk a) (hb : Blk b) : Blk (a ++ b) := by
  obtain ⟨ha1, x, t, rfl, hx⟩ := ha
  refine ⟨noAdjZero_append_head _ _ ha1 hb.1 ?_, x, t ++ b, rfl, hx⟩
  obtain ⟨_, y, u, rfl, hy⟩ := hb
  intro z v he
  cases he
  exact hy

private theorem w8_ofInt_ne_zero (n : Nat) (h1 : 0 < n) (h2 : n < 256) : W8 (n : Int) ≠ 0#8 := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat] at this
  omega

theorem varintEnc_noAdjZero (n : Nat) : NoAdjZero (varintEnc n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [varintEnc]
    split
    · trivial
    · rename_i h
      have hr := ih (n / 128) (by omega)
      generalize hv : varintEnc (n / 128) = v at hr
      cases v with
      | nil => trivial
      | cons y t =>
        refine ⟨fun hc => w8_ofInt_ne_zero (n % 128 + 128) (by omega) (by omega) ?_, hr⟩
        have := hc.1
        rwa [show ((n % 128 + 128 : Nat) : Int) = (n : Int) % 128 + 128 by omega]

theorem varintEnc_cons (n : Nat) : ∃ x t, varintEnc n = x :: t := by
  rw [varintEnc]
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- A non-zero number's varint starts with a non-zero byte. -/
theorem varintEnc_head_ne (n : Nat) (h : n ≠ 0) : ∀ x t, varintEnc n = x :: t → x ≠ 0#8 := by
  intro x t he
  rw [varintEnc] at he
  split at he
  · rename_i hn
    cases he
    exact w8_ofInt_ne_zero n (by omega) (by omega)
  · rename_i hn
    cases he
    have := w8_ofInt_ne_zero (n % 128 + 128) (by omega) (by omega)
    rwa [show ((n % 128 + 128 : Nat) : Int) = (n : Int) % 128 + 128 by omega] at this

/-- A non-zero number's varint ends with a non-zero byte (it is minimal). -/
theorem varintEnc_last_ne (n : Nat) (h : n ≠ 0) : ∀ x, (varintEnc n).getLast? = some x → x ≠ 0#8 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x hx
    rw [varintEnc] at hx
    split at hx
    · rename_i hn
      simp only [List.getLast?_singleton, Option.some.injEq] at hx
      subst hx
      exact w8_ofInt_ne_zero n (by omega) (by omega)
    · rename_i hn
      obtain ⟨y, t, he⟩ := varintEnc_cons (n / 128)
      rw [he, List.getLast?_cons_cons, ← he] at hx
      exact ih (n / 128) (by omega) (by omega) x hx

theorem varintEnc_blk (n : Nat) (h : n ≠ 0) : Blk (varintEnc n) := by
  obtain ⟨x, t, he⟩ := varintEnc_cons n
  exact ⟨varintEnc_noAdjZero n, x, t, he, varintEnc_head_ne n h x t he⟩

/-- A varint field (a non-zero tag, then any value) is a block. -/
theorem varintField_blk (tag v : Nat) (h : tag ≠ 0) : Blk (varintEnc tag ++ varintEnc v) := by
  have hb := varintEnc_blk tag h
  obtain ⟨_, x, t, he, hx⟩ := hb
  refine ⟨noAdjZero_append_last _ _ (varintEnc_noAdjZero tag) (varintEnc_noAdjZero v)
    (varintEnc_last_ne tag h), x, t ++ varintEnc v, by rw [he]; rfl, hx⟩

/-- A `bytes` field whose bytes are empty or a block is a block. -/
theorem bytesField_blk (tag : Nat) (d : List w8) (h : tag ≠ 0) (hd : d = [] ∨ Blk d) :
    Blk (varintEnc tag ++ varintEnc d.length ++ d) := by
  have hf := varintField_blk tag d.length h
  rcases hd with rfl | hd
  · simpa using hf
  · obtain ⟨hn, x, t, rfl, hx⟩ := hd
    refine ⟨noAdjZero_append_head _ _ hf.1 hn ?_, ?_⟩
    · intro y u he; cases he; exact hx
    · obtain ⟨_, z, v, he, hz⟩ := hf
      exact ⟨z, v ++ x :: t, by rw [he]; rfl, hz⟩

/-- **The first wire fact**: a record with its type set, no unknown fields, and data empty or a
block (a protobuf message's encoding with a field set, e.g. a `HardState`'s), is a block: no two
zero bytes adjacent, the first byte not zero. -/
theorem recEnc_blk (c : RecC) (ht : c.typ.isSome) (hu : c.uf = [])
    (hd : ∀ d, c.data = some d → d = [] ∨ Blk d) : Blk (recEnc c) := by
  rcases c with ⟨t, k, d, u⟩
  simp only at ht hu hd
  subst hu
  obtain ⟨t, rfl⟩ := Option.isSome_iff_exists.mp ht
  unfold recEnc
  simp only [Option.map_some, List.append_nil]
  have b1 : Blk (optVarintField 1 (some (uint.nat t))) := varintField_blk _ _ (by decide)
  have rest : ∀ xs : List w8, xs = [] ∨ Blk xs → Blk (optVarintField 1 (some (uint.nat t)) ++ xs) := by
    intro xs hx
    rcases hx with rfl | hx
    · simpa using b1
    · exact b1.append hx
  rw [List.append_assoc]
  apply rest
  have b2 : ∀ k : Option w32, optVarintField 2 (k.map uint.nat) = [] ∨
      Blk (optVarintField 2 (k.map uint.nat)) := by
    intro k; cases k
    · left; rfl
    · right; exact varintField_blk _ _ (by decide)
  have b3 : optBytesField 3 d = [] ∨ Blk (optBytesField 3 d) := by
    cases d with
    | none => left; rfl
    | some d => right; exact bytesField_blk _ d (by decide) (hd d rfl)
  rcases b2 k with h2 | h2 <;> rcases b3 with h3 | h3
  · left; rw [h2, h3]; rfl
  · right; rw [h2]; simpa using h3
  · right; rw [h3]; simpa using h2
  · right; exact h2.append h3

/-! ## The length word read over a block followed by zeros -/

theorem noAdjZero_get : ∀ (xs : List w8), NoAdjZero xs → ∀ (i : Nat) (h : i + 1 < xs.length),
    ¬(xs[i] = 0#8 ∧ xs[i + 1] = 0#8)
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | a :: b :: t, hx, i, h => by
    cases i with
    | zero => exact hx.1
    | succ i =>
      have := noAdjZero_get (b :: t) hx.2 i (by simp at h ⊢; omega)
      simpa using this

/-- **The second wire fact**: in a run `xs` with no two adjacent zeros followed by zeros, a length
word read at `k` (8 bytes, little-endian: its bytes 3 and 4 weigh `2^24` and `2^32`) has byte 3 or
byte 4 non-zero, or every byte from `k + 3` on is zero. -/
theorem window_len_or_zeros (xs : List w8) (z k : Nat) (hx : NoAdjZero xs) :
    let s := xs ++ List.replicate z 0#8
    s.getD (k + 3) 0#8 ≠ 0#8 ∨ s.getD (k + 4) 0#8 ≠ 0#8 ∨
      ∀ j, k + 3 ≤ j → s.getD j 0#8 = 0#8 := by
  intro s
  by_cases h3 : s.getD (k + 3) 0#8 = 0#8
  · by_cases h4 : s.getD (k + 4) 0#8 = 0#8
    · right; right
      have hlen : xs.length ≤ k + 4 := by
        refine Nat.le_of_not_lt fun hc => ?_
        have hc' : k + 3 + 1 < xs.length := by omega
        apply noAdjZero_get xs hx (k + 3) hc'
        constructor
        · have := h3
          simp only [s, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k + 3 < xs.length)] at this
          rw [List.getElem?_eq_getElem (by omega)] at this
          simpa using this
        · have := h4
          simp only [s, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k + 4 < xs.length)] at this
          rw [List.getElem?_eq_getElem (by omega)] at this
          simpa using this
      intro j hj
      by_cases hj3 : j = k + 3
      · subst hj3; exact h3
      · simp only [s, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : xs.length ≤ j),
          List.getElem?_replicate]
        split <;> rfl
    · right; left; exact h4
  · left; exact h3

end WalEnc
end EtcdGrove
end Perennial
