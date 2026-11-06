/-
Lean-first (no Rocq counterpart).

# The driver's codec, as pure functions (`examples/k8s/etcd3/k8s_etcd3.go`; stage 6c of
# `notes/k8s-etcd3-plan.md`)

- `DObj`: the driver's objects without their resource version: a name and a UID shorter than 256
  bytes (each length is one byte of the encoding) and a value;
- `encodeWith tag o` (`encodeWith`): the tag, the name's length, the name, the UID's length, the
  UID, the value; `decodeD`
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
namespace k8s_etcd3

open k8s

/-- The current encoding's tag (`tagV1`, `"v1:"`). -/
abbrev tagV1 : GoString := go!"v1:"

/-- The older encoding's tag (`tagV0`, `"v0:"`). -/
abbrev tagV0 : GoString := go!"v0:"

/-- **The driver's objects** without their resource version: a name and a UID, each shorter than 256
bytes (its length is one byte of the encoding), and a value. -/
def DObj : Type := { p : GoString × GoString × GoString // p.1.length < 256 ∧ p.2.1.length < 256 }

instance : DecidableEq DObj := inferInstanceAs (DecidableEq { p : GoString × GoString × GoString // _ })

/-- The object's name. -/
abbrev DObj.name (o : DObj) : GoString := o.1.1
/-- The object's UID. -/
abbrev DObj.uid (o : DObj) : GoString := o.1.2.1
/-- The object's value. -/
abbrev DObj.val (o : DObj) : GoString := o.1.2.2

/-- `encodeWith(tag, name, uid, val)`. -/
def encodeWith (tag name uid val : GoString) : GoString :=
  tag ++ [W8 (name.length : Int)] ++ name ++ [W8 (uid.length : Int)] ++ uid ++ val

/-- `decodeObj(data)`: the name, UID and value of either tag's encoding. -/
def decodeD (d : GoString) : Option (GoString × GoString × GoString) :=
  if d.length < 4 then none
  else if d.take 3 ≠ tagV1 ∧ d.take 3 ≠ tagV0 then none
  else
    let n := (d.getD 3 (W8 0)).toNat
    if d.length < 5 + n then none
    else
      let m := (d.getD (4 + n) (W8 0)).toNat
      if d.length < 5 + n + m then none
      else some ((d.drop 4).take n, (d.drop (5 + n)).take m, d.drop (5 + n + m))

theorem decodeD_encode (tag : GoString) (ht : tag = tagV1 ∨ tag = tagV0) (name uid val : GoString)
    (hn : name.length < 256) (hu : uid.length < 256) :
    decodeD (encodeWith tag name uid val) = some (name, uid, val) := by
  have h3 : tag.length = 3 := by rcases ht with rfl | rfl <;> rfl
  have hb : (W8 (name.length : Int)).toNat = name.length := by
    simp only [W8, BitVec.toNat_ofInt]
    omega
  have hbu : (W8 (uid.length : Int)).toNat = uid.length := by
    simp only [W8, BitVec.toNat_ofInt]
    omega
  unfold decodeD encodeWith
  have hlen : (tag ++ [W8 (name.length : Int)] ++ name ++ [W8 (uid.length : Int)] ++ uid ++
      val).length = 5 + name.length + uid.length + val.length := by simp [h3]; omega
  have htake : (tag ++ [W8 (name.length : Int)] ++ name ++ [W8 (uid.length : Int)] ++ uid ++
      val).take 3 = tag := by
    simp [List.take_append, h3]
  have hget : (tag ++ [W8 (name.length : Int)] ++ name ++ [W8 (uid.length : Int)] ++ uid ++
      val).getD 3 (W8 0) = W8 (name.length : Int) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, h3]
  have hget2 : (tag ++ [W8 (name.length : Int)] ++ name ++ [W8 (uid.length : Int)] ++ uid ++
      val).getD (4 + name.length) (W8 0) = W8 (uid.length : Int) := by
    have e : tag ++ [W8 (name.length : Int)] ++ name ++ [W8 (uid.length : Int)] ++ uid ++ val =
        (tag ++ [W8 (name.length : Int)] ++ name) ++ (W8 (uid.length : Int) :: (uid ++ val)) := by
      simp
    have hl : (tag ++ [W8 (name.length : Int)] ++ name).length = 4 + name.length := by
      simp [h3]; omega
    rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, Nat.sub_self]
    rfl
  rw [hlen, htake, hget, hb]
  have hnot : ¬ (tag ≠ tagV1 ∧ tag ≠ tagV0) := by
    rcases ht with rfl | rfl <;> simp
  simp only [hnot, ↓reduceIte]
  have h1 : ¬ 5 + name.length + uid.length + val.length < 4 := by omega
  have h2 : ¬ 5 + name.length + uid.length + val.length < 5 + name.length := by omega
  simp only [h1, h2, ↓reduceIte]
  rw [hget2, hbu]
  have h4 : ¬ 5 + name.length + uid.length + val.length < 5 + name.length + uid.length := by omega
  simp only [h4, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp [List.drop_append, h3, List.take_append]
  · have e : tag ++ [W8 (name.length : Int)] ++ name ++ [W8 (uid.length : Int)] ++ uid ++ val =
        (tag ++ [W8 (name.length : Int)] ++ name ++ [W8 (uid.length : Int)]) ++ (uid ++ val) := by
      simp
    rw [e, List.drop_left' (by simp [h3]; omega), List.take_left' rfl]
  · rw [show 5 + name.length + uid.length = (tag ++ [W8 (name.length : Int)] ++ name ++
        [W8 (uid.length : Int)] ++ uid).length by simp [h3]; omega]
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
def dzero : DObj := ⟨([], [], []), by decide⟩

/-- The codec's decoding, as an object: a name and a UID shorter than 256 bytes (always: their
lengths are bytes). -/
def decodeObjD (d : GoString) : Option DObj :=
  (decodeD d).bind fun p =>
    if h : p.1.length < 256 ∧ p.2.1.length < 256 then some ⟨p, h⟩ else none

theorem decodeObjD_encode (tag : GoString) (ht : tag = tagV1 ∨ tag = tagV0) (o : DObj) :
    decodeObjD (encodeWith tag o.name o.uid o.val) = some o := by
  unfold decodeObjD
  rw [decodeD_encode tag ht o.name o.uid o.val o.2.1 o.2.2]
  simp only [Option.bind_some, o.2, and_self, ↓reduceDIte]
  rfl

/-- A decoding's parts fill the data: the tag, the name's length byte, the name, the UID's length
byte, the UID and the value; the name and the UID are shorter than 256 bytes. -/
theorem decodeD_length (d n u v : GoString) (h : decodeD d = some (n, u, v)) :
    5 + n.length + u.length + v.length = d.length ∧ n.length < 256 ∧ u.length < 256 := by
  unfold decodeD at h
  split at h
  · cases h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have := (d.getD 3 (W8 0)).isLt
  rename_i h1 h2
  have := (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).isLt
  simp only [List.length_take, List.length_drop]
  omega

/-- A decoded name is shorter than 256 bytes (its length is a byte); so is a decoded UID. -/
theorem decodeD_name_lt (d n u v : GoString) (h : decodeD d = some (n, u, v)) :
    n.length < 256 ∧ u.length < 256 :=
  (decodeD_length d n u v h).2

/-- The codec's decoding as an object is `decodeD`'s. -/
theorem decodeObjD_of (d n u v : GoString) (h : decodeD d = some (n, u, v)) :
    decodeObjD d = some ⟨(n, u, v), decodeD_name_lt d n u v h⟩ := by
  unfold decodeObjD; rw [h]
  simp [decodeD_name_lt d n u v h]

theorem decodeObjD_none (d : GoString) (h : decodeD d = none) : decodeObjD d = none := by
  unfold decodeObjD; rw [h]; rfl

/-- **Re-encoding a decoded object keeps its length** (either tag is three bytes): a no-op update,
which writes the object read with the current tag, writes no more than it read. -/
theorem decodeObjD_encode_length (d : GoString) (o : DObj) (h : decodeObjD d = some o) :
    (encodeWith tagV1 o.name o.uid o.val).length = d.length := by
  unfold decodeObjD at h
  cases hd : decodeD d with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      have := (decodeD_length d p.1 p.2.1 p.2.2 hd).1
      simp only [encodeWith, DObj.name, DObj.uid, DObj.val, List.length_append, List.length_cons,
        List.length_nil]
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
  encode o := encodeWith tagV1 o.name o.uid o.val
  decode := decodeObjD
  decode_encode o := decodeObjD_encode tagV1 (.inl rfl) o
  encode_ne_nil o := by simp [encodeWith]
  fromS v := some (v, false)
  toS d v := v = d
  fromS_toS d v h := by rw [h]
  parseRV := parseRVD
  fmtRV := rvStr
  parse_fmt := parseRVD_rvStr
  parse_empty := rfl
  fmt_zero := rfl
  uid o := o.uid
  zero := dzero

end k8s_etcd3
end EtcdGrove
end Perennial
