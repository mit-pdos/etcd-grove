/-
Lean-first (no Rocq counterpart).

# The driver's codec, as pure functions (`examples/k8s/etcd3/k8s_etcd3.go`; stage 6c of
# `notes/k8s-etcd3-plan.md`)

- `DObj`: the driver's objects without their resource version: a namespace, name, UID, node and
  app shorter than 256 bytes (each length is one byte of the encoding) and a value (stage 7e);
  `o.toObj n` is Go's record of it at resource version `n`;
- `encodeWith tag v` (`encodeWith`, on the Go record): the tag, then the namespace, name, UID,
  node and app each as a length byte and its bytes (`putF`, `putField`), then the value;
  `decodeD` (`decodeObj`, through `getFieldD`, `getField`): either tag's encoding back
  (`decodeD_encode`);
- `rvStr n`: the versioner's string form of a resource version (empty for `0`, its eight bytes
  big-endian otherwise), and `parseRVD` (`parseRV`) back (`parseRVD_rvStr`);
- `driverCodec`: the store's `ObjCodec` of the driver (the identity transformer).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Contract
public import Code.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

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

/-- **The driver's objects** without their resource version (stage 7e: the namespace/name split,
the node and the app label): the namespace, name, UID, node and app, each shorter than 256 bytes
(its length is one byte of the encoding), and a value. -/
structure DObj where
  ns : GoString
  name : GoString
  uid : GoString
  val : GoString
  node : GoString
  app : GoString
  fits : ns.length < 256 ∧ name.length < 256 ∧ uid.length < 256 ∧ node.length < 256 ∧
    app.length < 256

theorem DObj.ext_iff' (a b : DObj) :
    a = b ↔ a.ns = b.ns ∧ a.name = b.name ∧ a.uid = b.uid ∧ a.val = b.val ∧ a.node = b.node ∧
      a.app = b.app := by
  constructor
  · rintro rfl; simp
  · cases a; cases b; simp only [DObj.mk.injEq]; intro h; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩

instance : DecidableEq DObj := fun a b => decidable_of_iff _ (DObj.ext_iff' a b).symm

section go
variable [GooseExts]

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj)

/-- Go's record of an object at the resource version `n`. -/
abbrev DObj.toObj (o : DObj) (n : w64) : Obj := ⟨o.ns, o.name, o.uid, o.val, o.node, o.app, n, false⟩

/-- A Go record's fields fit a `DObj` (each length a byte). -/
def fitsD (v : Obj) : Prop :=
  v.Namespace'.length < 256 ∧ v.Name'.length < 256 ∧ v.UID'.length < 256 ∧ v.Node'.length < 256 ∧
    v.App'.length < 256

instance (v : Obj) : Decidable (fitsD v) := by unfold fitsD; infer_instance

/-- The object of a Go record whose fields fit (its resource version dropped). -/
def DObj.ofObj (v : Obj) (h : fitsD v) : DObj :=
  ⟨v.Namespace', v.Name', v.UID', v.Value', v.Node', v.App', h⟩

/-- A record with no annotation, at another resource version, is its object's. -/
theorem DObj.ofObj_toObj_rv (v : Obj) (h : fitsD v) (ha : v.Annotated' = false) (n : w64) :
    (DObj.ofObj v h).toObj n = { v with ResourceVersion' := n } := by
  cases v; simp_all [DObj.ofObj]

theorem DObj.toObj_fits (o : DObj) (n : w64) : fitsD (o.toObj n) := o.fits

@[simp] theorem DObj.ofObj_toObj (o : DObj) (n : w64) (h : fitsD (o.toObj n)) :
    DObj.ofObj (o.toObj n) h = o := rfl

theorem DObj.toObj_ofObj (v : Obj) (h : fitsD v) (ha : v.Annotated' = false) :
    (DObj.ofObj v h).toObj v.ResourceVersion' = v := by
  cases v; simp_all [DObj.ofObj]

/-- `putField(out, f)`: `out`, `f`'s length (one byte) and `f`. -/
def putF (out f : GoString) : GoString := out ++ [W8 (f.length : Int)] ++ f

/-- `encodeWith(tag, o)`: the tag, the namespace, name, UID, node and app as length-prefixed
fields, and the value. -/
def encodeWith (tag : GoString) (v : Obj) : GoString :=
  putF (putF (putF (putF (putF tag v.Namespace') v.Name') v.UID') v.Node') v.App' ++ v.Value'

/-- `getField(data, i)`: the length-prefixed field at `i` and the index after it. -/
def getFieldD (d : GoString) (i : Nat) : Option (GoString × Nat) :=
  if d.length < i + 1 then none
  else
    let n := (d.getD i (W8 0)).toNat
    if d.length < i + 1 + n then none else some ((d.drop (i + 1)).take n, i + 1 + n)

/-- `decodeObj(data)`: either tag's encoding back, as a record at resource version `0`. -/
def decodeD (d : GoString) : Option Obj :=
  if d.length < 3 then none
  else if d.take 3 ≠ tagV1 ∧ d.take 3 ≠ tagV0 then none
  else
    match getFieldD d 3 with
    | none => none
    | some (ns, i1) =>
    match getFieldD d i1 with
    | none => none
    | some (name, i2) =>
    match getFieldD d i2 with
    | none => none
    | some (uid, i3) =>
    match getFieldD d i3 with
    | none => none
    | some (node, i4) =>
    match getFieldD d i4 with
    | none => none
    | some (app, i5) => some ⟨ns, name, uid, d.drop i5, node, app, 0, false⟩

/-- A field read: it fits in the data, its length is a byte, and the index after it is past it. -/
theorem getFieldD_some (d : GoString) (i : Nat) (f : GoString) (j : Nat)
    (h : getFieldD d i = some (f, j)) : j = i + 1 + f.length ∧ j ≤ d.length ∧ f.length < 256 := by
  unfold getFieldD at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have := (d.getD i (W8 0)).isLt
  simp only [List.length_take, List.length_drop]
  omega

/-- **A field written is read back**, from any data `putF pre f` begins. -/
theorem getFieldD_putF (pre f d : GoString) (hf : f.length < 256) (hp : putF pre f <+: d) :
    getFieldD d pre.length = some (f, (putF pre f).length) := by
  obtain ⟨t, rfl⟩ := hp
  have hb : (W8 (f.length : Int)).toNat = f.length := by
    simp only [W8, BitVec.toNat_ofInt]; omega
  have hlen : (putF pre f ++ t).length = pre.length + 1 + f.length + t.length := by
    simp [putF]; omega
  have hget : (putF pre f ++ t).getD pre.length (W8 0) = W8 (f.length : Int) := by
    simp [putF, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  unfold getFieldD
  rw [hlen, hget, hb, if_neg (by omega)]
  dsimp only
  rw [if_neg (by omega)]
  have e : pre ++ [W8 (f.length : Int)] ++ f ++ t = (pre ++ [W8 (f.length : Int)]) ++ (f ++ t) := by
    simp
  simp only [putF, List.length_append, List.length_singleton, Option.some.injEq, Prod.mk.injEq,
    and_true]
  rw [e, List.drop_left' (by simp), List.take_left' rfl]

/-- **Decoding inverts the encoding**, for either tag and fields that fit. -/
theorem decodeD_encode (tag : GoString) (ht : tag = tagV1 ∨ tag = tagV0) (v : Obj)
    (hv : fitsD v) : decodeD (encodeWith tag v) = some { v with ResourceVersion' := 0, Annotated' := false } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  have h3t : tag.length = 3 := by rcases ht with rfl | rfl <;> rfl
  have htake : (encodeWith tag v).take 3 = tag := by
    simp [encodeWith, putF, List.take_append, h3t]
  have hl : ¬ (encodeWith tag v).length < 3 := by simp [encodeWith, putF]; omega
  unfold decodeD
  rw [if_neg hl, htake]
  have hnot : ¬ (tag ≠ tagV1 ∧ tag ≠ tagV0) := by rcases ht with rfl | rfl <;> simp
  rw [if_neg hnot]
  rw [show (3 : Nat) = tag.length from h3t.symm]
  rw [getFieldD_putF tag _ _ h1 (by simp [encodeWith, putF])]
  dsimp only
  rw [getFieldD_putF _ _ _ h2 (by simp [encodeWith, putF])]
  dsimp only
  rw [getFieldD_putF _ _ _ h3 (by simp [encodeWith, putF])]
  dsimp only
  rw [getFieldD_putF _ _ _ h4 (by simp [encodeWith, putF])]
  dsimp only
  rw [getFieldD_putF _ _ _ h5 (by simp [encodeWith, putF])]
  dsimp only
  rw [show encodeWith tag v = putF (putF (putF (putF (putF tag v.Namespace') v.Name') v.UID')
    v.Node') v.App' ++ v.Value' from rfl, List.drop_left]

/-- The encoding's length: the tag, a byte and the bytes of each field, the value. -/
theorem encodeWith_length (tag : GoString) (v : Obj) :
    (encodeWith tag v).length = tag.length + 5 + v.Namespace'.length + v.Name'.length +
      v.UID'.length + v.Node'.length + v.App'.length + v.Value'.length := by
  simp [encodeWith, putF]; omega

/-- A decoded record's fields fit, its resource version is `0` (and it carries no annotation), and re-encoding it with a
three-byte tag gives data of the same length. -/
theorem decodeD_some (d : GoString) (v : Obj) (h : decodeD d = some v) :
    fitsD v ∧ v.ResourceVersion' = 0 ∧ (encodeWith tagV1 v).length = d.length ∧
      v.Annotated' = false := by
  unfold decodeD at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hl _
  split at h
  · cases h
  rename_i ns i1 h1
  split at h
  · cases h
  rename_i name i2 h2
  split at h
  · cases h
  rename_i uid i3 h3
  split at h
  · cases h
  rename_i node i4 h4
  split at h
  · cases h
  rename_i app i5 h5
  cases h
  obtain ⟨e1, l1, f1⟩ := getFieldD_some _ _ _ _ h1
  obtain ⟨e2, l2, f2⟩ := getFieldD_some _ _ _ _ h2
  obtain ⟨e3, l3, f3⟩ := getFieldD_some _ _ _ _ h3
  obtain ⟨e4, l4, f4⟩ := getFieldD_some _ _ _ _ h4
  obtain ⟨e5, l5, f5⟩ := getFieldD_some _ _ _ _ h5
  refine ⟨⟨f1, f2, f3, f4, f5⟩, rfl, ?_, rfl⟩
  rw [encodeWith_length]
  simp only [List.length_drop]
  have : tagV1.length = 3 := rfl
  omega

/-- The two tags' encodings differ (the seeds' data is not the current encoding: D30g). -/
theorem encodeWith_v0_ne_v1 (v w : Obj) : encodeWith tagV0 v ≠ encodeWith tagV1 w := by
  intro h
  have := congrArg (List.take 3) h
  simp [encodeWith, putF, List.take_append] at this

end go

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
def dzero : DObj := ⟨[], [], [], [], [], [], by decide⟩

/-- The string form of a resource version is empty only for `0`. -/
theorem rvStr_nil (n : w64) (h : rvStr n = []) : n = 0 := by
  unfold rvStr at h
  by_cases hn : n = 0
  · exact hn
  · rw [if_neg hn] at h; simp [rvBytes] at h

/-! ## A list's items as a plain value (`encodeItems`, stage 7e) -/

section items
variable [GooseExts]

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj)

/-- One item of `encodeItems`: its resource version, its encoding's length and its encoding. -/
def encItemL (o : Obj) : GoString :=
  rvBytes o.ResourceVersion' ++ rvBytes (W64 ((encodeWith tagV1 o).length : Int)) ++ encodeWith tagV1 o

/-- `encodeItems(items)`: the items' `encItemL`s, in order (the loop's `append`s). -/
def encItemsL (os : List Obj) : GoString := os.foldl (fun acc o => acc ++ encItemL o) []

theorem encItemsL_foldl (os : List Obj) (acc : GoString) :
    os.foldl (fun acc o => acc ++ encItemL o) acc = acc ++ (os.map encItemL).flatten := by
  induction os generalizing acc with
  | nil => simp
  | cons o os ih => simp [ih, List.append_assoc]

theorem encItemsL_eq (os : List Obj) : encItemsL os = (os.map encItemL).flatten := by
  unfold encItemsL; rw [encItemsL_foldl]; simp

/-- The objects `encodeItems` is injective on: fields that fit, no annotation, an encoding shorter
than `2^63` (the driver's: values are short). -/
def itemOk (o : Obj) : Prop :=
  fitsD o ∧ o.Annotated' = false ∧ (encodeWith tagV1 o).length < 2 ^ 63

theorem rvBytes_length (n : w64) : (rvBytes n).length = 8 := rfl

theorem rvBytes_inj (a b : w64) (h : rvBytes a = rvBytes b) : a = b := by
  rw [← bytesBE_rvBytes a, ← bytesBE_rvBytes b, h]

/-- One item's encoding is self-delimiting: it is read back from any data it begins. -/
theorem encItemL_prefix (a b : Obj) (ra rb : GoString) (ha : itemOk a) (hb : itemOk b)
    (h : encItemL a ++ ra = encItemL b ++ rb) : a = b ∧ ra = rb := by
  have hlen : ∀ o : Obj, itemOk o →
      (W64 ((encodeWith tagV1 o).length : Int)).toNat = (encodeWith tagV1 o).length := by
    intro o ho; simp only [W64, BitVec.toNat_ofInt]; have := ho.2.2; omega
  unfold encItemL at h
  simp only [List.append_assoc] at h
  have h1 := congrArg (List.take 8) h
  rw [List.take_left' (rvBytes_length _), List.take_left' (rvBytes_length _)] at h1
  have hrv := rvBytes_inj _ _ h1
  have h2 := congrArg (List.drop 8) h
  rw [List.drop_left' (rvBytes_length _), List.drop_left' (rvBytes_length _)] at h2
  have h3 := congrArg (List.take 8) h2
  rw [List.take_left' (rvBytes_length _), List.take_left' (rvBytes_length _)] at h3
  have hn := congrArg BitVec.toNat (rvBytes_inj _ _ h3)
  rw [hlen a ha, hlen b hb] at hn
  have h4 := congrArg (List.drop 8) h2
  rw [List.drop_left' (rvBytes_length _), List.drop_left' (rvBytes_length _)] at h4
  have he : encodeWith tagV1 a = encodeWith tagV1 b := by
    have := congrArg (List.take (encodeWith tagV1 a).length) h4
    rw [List.take_left' rfl, hn, List.take_left' rfl] at this
    exact this
  have hr : ra = rb := by
    rw [he] at h4; exact List.append_cancel_left h4
  refine ⟨?_, hr⟩
  have hd := decodeD_encode tagV1 (.inl rfl) a ha.1
  rw [he, decodeD_encode tagV1 (.inl rfl) b hb.1] at hd
  have hd := Option.some.inj hd
  have ha2 := ha.2.1; have hb2 := hb.2.1
  cases a; cases b
  simp only [Obj.mk.injEq] at hd hrv ha2 hb2 ⊢
  simp_all

/-- **`encodeItems` is injective** on the items the driver makes (`itemOk`). -/
theorem encItemsL_inj (xs ys : List Obj) (ha : ∀ o ∈ xs, itemOk o) (hb : ∀ o ∈ ys, itemOk o)
    (h : encItemsL xs = encItemsL ys) : xs = ys := by
  rw [encItemsL_eq, encItemsL_eq] at h
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b ys => simp [encItemL] at h; exact absurd h.1 (by simp [rvBytes])
  | cons a xs ih =>
    cases ys with
    | nil => simp [encItemL] at h; exact absurd h.1 (by simp [rvBytes])
    | cons b ys =>
      simp only [List.map_cons, List.flatten_cons] at h
      obtain ⟨rfl, hr⟩ := encItemL_prefix a b _ _ (ha a (by simp)) (hb b (by simp)) h
      rw [ih ys (fun o ho => ha o (by simp [ho])) (fun o ho => hb o (by simp [ho])) hr]

end items

section go
variable [GooseExts]

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj)

/-- The codec's decoding, as an object (its fields always fit: their lengths are bytes). -/
def decodeObjD (d : GoString) : Option DObj :=
  (decodeD d).bind fun v => if h : fitsD v then some (DObj.ofObj v h) else none

theorem decodeObjD_encode (tag : GoString) (ht : tag = tagV1 ∨ tag = tagV0) (o : DObj) (n : w64) :
    decodeObjD (encodeWith tag (o.toObj n)) = some o := by
  unfold decodeObjD
  rw [decodeD_encode tag ht _ (o.toObj_fits n)]
  simp only [Option.bind_some]
  split
  · rfl
  · rename_i h; exact absurd o.fits h

/-- The codec's decoding as an object is `decodeD`'s. -/
theorem decodeObjD_of (d : GoString) (v : Obj) (h : decodeD d = some v) :
    decodeObjD d = some (DObj.ofObj v (decodeD_some d v h).1) := by
  unfold decodeObjD; rw [h]
  simp [(decodeD_some d v h).1]

theorem decodeObjD_none (d : GoString) (h : decodeD d = none) : decodeObjD d = none := by
  unfold decodeObjD; rw [h]; rfl

/-- **Re-encoding a decoded object keeps its length** (either tag is three bytes): a no-op update,
which writes the object read with the current tag, writes no more than it read. -/
theorem decodeObjD_encode_length (d : GoString) (o : DObj) (n : w64) (h : decodeObjD d = some o) :
    (encodeWith tagV1 (o.toObj n)).length = d.length := by
  unfold decodeObjD at h
  cases hd : decodeD d with
  | none => rw [hd] at h; cases h
  | some v =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      rw [← (decodeD_some d v hd).2.2.1, encodeWith_length, encodeWith_length]
      rfl
    · cases h

/-- **The store's codec of the driver** (`ObjCodec`): the current encoding, decoding either; the
identity transformer (never stale); the versioner's string form of resource versions. -/
def driverCodec : ObjCodec DObj where
  encode o := encodeWith tagV1 (o.toObj 0)
  decode := decodeObjD
  decode_encode o := decodeObjD_encode tagV1 (.inl rfl) o 0
  encode_ne_nil o := by simp [encodeWith, putF]
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

end go

end k8s_etcd3
end EtcdGrove
end Perennial
