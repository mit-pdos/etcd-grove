/-
Lean-first (no Rocq counterpart).

# The driver's codec, as pure functions (`examples/k8setcd3/k8setcd3.go`; stage 6c of
# `notes/k8s-etcd3-plan.md`)

- `DObj`: the driver's objects without their resource version: a name shorter than 256 bytes (its
  length is one byte of the encoding) and a value;
- `encodeWith tag o` (`encodeWith`): the tag, the name's length, the name, the value; `decodeD`
  (`decodeObj`): either tag's encoding back (`decodeD_encode`);
- `rvStr n`: the versioner's string form of a resource version (empty for `0`, its eight bytes
  big-endian otherwise), and `parseRVD` (`parseRV`) back (`parseRVD_rvStr`);
- `driverCodec`: the store's `ObjCodec` of the driver (the identity transformer).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Contract

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open k8s

/-- The current encoding's tag (`tagV1`, `"v1:"`). -/
abbrev tagV1 : GoString := go!"v1:"

/-- The older encoding's tag (`tagV0`, `"v0:"`). -/
abbrev tagV0 : GoString := go!"v0:"

/-- **The driver's objects** without their resource version: a name shorter than 256 bytes and a
value. -/
def DObj : Type := { p : GoString × GoString // p.1.length < 256 }

instance : DecidableEq DObj := inferInstanceAs (DecidableEq { p : GoString × GoString // _ })

/-- `encodeWith(tag, name, val)`. -/
def encodeWith (tag name val : GoString) : GoString :=
  tag ++ [W8 (name.length : Int)] ++ name ++ val

/-- `decodeObj(data)`: the name and value of either tag's encoding. -/
def decodeD (d : GoString) : Option (GoString × GoString) :=
  if d.length < 4 then none
  else if d.take 3 ≠ tagV1 ∧ d.take 3 ≠ tagV0 then none
  else
    let n := (d.getD 3 (W8 0)).toNat
    if d.length < 4 + n then none
    else some ((d.drop 4).take n, d.drop (4 + n))

theorem decodeD_encode (tag : GoString) (ht : tag = tagV1 ∨ tag = tagV0) (name val : GoString)
    (hn : name.length < 256) :
    decodeD (encodeWith tag name val) = some (name, val) := by
  have h3 : tag.length = 3 := by rcases ht with rfl | rfl <;> rfl
  have hb : (W8 (name.length : Int)).toNat = name.length := by
    simp only [W8, BitVec.toNat_ofInt]
    omega
  unfold decodeD encodeWith
  have hlen : (tag ++ [W8 (name.length : Int)] ++ name ++ val).length =
      4 + name.length + val.length := by simp [h3]; omega
  have htake : (tag ++ [W8 (name.length : Int)] ++ name ++ val).take 3 = tag := by
    simp [List.take_append, h3]
  have hget : (tag ++ [W8 (name.length : Int)] ++ name ++ val).getD 3 (W8 0) =
      W8 (name.length : Int) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, h3]
  rw [hlen, htake, hget, hb]
  have hnot : ¬ (tag ≠ tagV1 ∧ tag ≠ tagV0) := by
    rcases ht with rfl | rfl <;> simp
  simp only [hnot, ↓reduceIte]
  have h1 : ¬ 4 + name.length + val.length < 4 := by omega
  have h2 : ¬ 4 + name.length + val.length < 4 + name.length := by omega
  simp only [h1, h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
  constructor
  · simp [List.drop_append, h3, List.take_append]
  · rw [show 4 + name.length = (tag ++ [W8 (name.length : Int)] ++ name).length by
      simp [h3]; omega]
    exact List.drop_left

/-! ## Resource versions -/

/-- A resource version's eight bytes, big-endian. -/
def rvBytes (n : w64) : GoString :=
  [n.extractLsb' 56 8, n.extractLsb' 48 8, n.extractLsb' 40 8, n.extractLsb' 32 8,
    n.extractLsb' 24 8, n.extractLsb' 16 8, n.extractLsb' 8 8, n.extractLsb' 0 8]

/-- **The versioner's string form of a resource version**: empty for `0`. -/
def rvStr (n : w64) : GoString := if n = 0 then [] else rvBytes n

/-- `parseRV`'s loop: `n = n<<8 | uint64(s[i])`. -/
def bytesBE (s : GoString) : w64 :=
  s.foldl (fun n b => n <<< 8 ||| b.zeroExtend 64) 0

/-- `parseRV(s)`: empty is `0`, eight bytes their number, anything else an error. -/
def parseRVD (s : GoString) : Option w64 :=
  if s.length = 0 then some 0 else if s.length = 8 then some (bytesBE s) else none

theorem bytesBE_rvBytes (n : w64) : bytesBE (rvBytes n) = n := by
  simp only [bytesBE, rvBytes, List.foldl_cons, List.foldl_nil]
  -- bit by bit (not `bv_decide`, whose proof rests on native evaluation)
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft]
  iterate 64 (rcases i with _ | i; · simp)
  omega

theorem parseRVD_rvStr (n : w64) : parseRVD (rvStr n) = some n := by
  unfold rvStr
  by_cases h : n = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte, parseRVD]
    have hb := bytesBE_rvBytes n
    simp only [rvBytes] at hb ⊢
    simp [hb]

/-! ## The store's codec of the driver -/

/-- The empty object (`NewFunc()`'s, `&Obj{}`). -/
def dzero : DObj := ⟨([], []), by decide⟩

/-- The codec's decoding, as an object: a name shorter than 256 bytes (always: its length is a
byte). -/
def decodeObjD (d : GoString) : Option DObj :=
  (decodeD d).bind fun p => if h : p.1.length < 256 then some ⟨p, h⟩ else none

theorem decodeObjD_encode (tag : GoString) (ht : tag = tagV1 ∨ tag = tagV0) (o : DObj) :
    decodeObjD (encodeWith tag o.1.1 o.1.2) = some o := by
  unfold decodeObjD
  rw [decodeD_encode tag ht o.1.1 o.1.2 o.2]
  simp only [Option.bind_some, o.2, ↓reduceDIte]
  rfl

/-- A decoded name is shorter than 256 bytes (its length is a byte). -/
theorem decodeD_name_lt (d n v : GoString) (h : decodeD d = some (n, v)) : n.length < 256 := by
  unfold decodeD at h
  split at h
  · cases h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have := (d.getD 3 (W8 0)).isLt
  simp only [List.length_take]
  omega

/-- The codec's decoding as an object is `decodeD`'s. -/
theorem decodeObjD_of (d n v : GoString) (h : decodeD d = some (n, v)) :
    decodeObjD d = some ⟨(n, v), decodeD_name_lt d n v h⟩ := by
  unfold decodeObjD; rw [h]
  simp [decodeD_name_lt d n v h]

theorem decodeObjD_none (d : GoString) (h : decodeD d = none) : decodeObjD d = none := by
  unfold decodeObjD; rw [h]; rfl

/-- A decoding's parts fill the data: the tag, the name's length byte, the name and the value. -/
theorem decodeD_length (d n v : GoString) (h : decodeD d = some (n, v)) :
    4 + n.length + v.length = d.length := by
  unfold decodeD at h
  split at h
  · cases h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.length_take, List.length_drop]
  omega

/-- **Re-encoding a decoded object keeps its length** (either tag is three bytes): a no-op update,
which writes the object read with the current tag, writes no more than it read. -/
theorem decodeObjD_encode_length (d : GoString) (o : DObj) (h : decodeObjD d = some o) :
    (encodeWith tagV1 o.1.1 o.1.2).length = d.length := by
  unfold decodeObjD at h
  cases hd : decodeD d with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      have := decodeD_length d p.1 p.2 hd
      simp only [encodeWith, List.length_append, List.length_cons, List.length_nil]
      have h3 : tagV1.length = 3 := rfl
      omega
    · cases h

/-- The string form of a resource version is empty only for `0`. -/
theorem rvStr_nil (n : w64) (h : rvStr n = []) : n = 0 := by
  unfold rvStr at h
  by_cases hn : n = 0
  · exact hn
  · rw [if_neg hn] at h; simp [rvBytes] at h

/-- **The store's codec of the driver** (`ObjCodec`): the current encoding, decoding either; the
identity transformer (never stale); the versioner's string form of resource versions. -/
def driverCodec : ObjCodec DObj where
  encode o := encodeWith tagV1 o.1.1 o.1.2
  decode := decodeObjD
  decode_encode o := decodeObjD_encode tagV1 (.inl rfl) o
  fromS v := some (v, false)
  toS d v := v = d
  fromS_toS d v h := by rw [h]
  parseRV := parseRVD
  fmtRV := rvStr
  parse_fmt := parseRVD_rvStr
  parse_empty := rfl
  zero := dzero

end k8setcd3
end EtcdGrove
end Perennial
