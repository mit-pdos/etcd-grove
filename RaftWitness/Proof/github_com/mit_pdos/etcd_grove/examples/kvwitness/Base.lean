/-
Lean-first (no Rocq counterpart).

# The key-value store: package initialization and the pure model (2026-10-10; the store,
2026-10-19)

`examples/kvwitness/kv.go` has no package-level variable (`opPut`, `opGet`, `opAppend`, `maxIndex`
and `maxSeq` are constants), so its package fact is `True`; the packages it imports have
theirs (Perennial's `context`, `encoding/binary`, `sync`; etcd-grove's raft and `raftpb`,
`Proof/go_etcd_io/raft/v3/Base.lean`; the porcupine driver's and porcupine's).

The pure model: an operation's encoding (`encodeOp`: the proposing replica and its
sequence number, little-endian, the kind, the key's length, the key, the value), what
`decode` reads back (`decodeOp`), and the store's state machine over the client log
(`kvFold`, over `KVMap`, every key's value: a `Put` sets its key, an `Append` appends to it,
anything else -- a `Get`, a datum that is no operation -- leaves the store). An operation
answers its key's value after it (`dkey`). The client log holds each operation once
(`firstOcc`, `Protocol/Model.lean`), which is what `apply`'s table of applied encodings
(`AppliedOk`) mirrors. (Until 2026-10-19 the example was a register: one value, `Put` and
`Get`.)
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.Link
public import RaftWitness.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.kvwitness
public import Perennial.Proof.encoding.binary
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.kvwitness

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.kvwitness

namespace EtcdGrove

/-! ## The pure model -/

/-- `opPut`. -/
def opPutB : w8 := W8 1

/-- `opGet`. -/
def opGetB : w8 := W8 2

/-- `opRead` (2026-10-13): the kind of a read's context. -/
def opReadB : w8 := W8 3

/-- `opAppend` (2026-10-19). -/
def opAppendB : w8 := W8 4

/-- What `encode(replica, seq, kind, key, val)` returns: the 25-byte header (the replica, the
sequence number, the kind, the key's length), the key, the value. -/
def encodeOp (replica seq : w64) (kind : w8) (key val : List w8) : List w8 :=
  u64Le replica ++ u64Le seq ++ [kind] ++ u64Le (W64 key.length) ++ key ++ val

/-- What `decode` reads back: `none` for fewer than 25 bytes, or a key length past the end. -/
def decodeOp (d : List w8) : Option (w64 × w64 × w8 × List w8 × List w8) :=
  if 25 ≤ d.length then
    if uint.Z (leToU64 ((d.drop 17).take 8)) ≤ (d.length : Int) - 25 then
      some (leToU64 (d.take 8), leToU64 ((d.drop 8).take 8), d.getD 16 (W8 0),
        (d.drop 25).take (uint.nat (leToU64 ((d.drop 17).take 8))),
        (d.drop 25).drop (uint.nat (leToU64 ((d.drop 17).take 8))))
    else none
  else none

/-- An operation's key: its replica and sequence number. -/
def opKey (d : List w8) : Option (w64 × w64) :=
  (decodeOp d).map (fun x => (x.1, x.2.1))

/-- The store's state: every key's value (`[]`, the empty string, for a key never set). -/
abbrev KVMap := List w8 → List w8

/-- The empty store. -/
def kvEmpty : KVMap := fun _ => []

/-- `m` with `k` set to `v`. -/
def kvUpd (m : KVMap) (k v : List w8) : KVMap := fun k' => if k' = k then v else m k'

/-- The store after an operation of kind `kind` on `key` with value `val`: a `Put` sets the
key, an `Append` appends to it, anything else (a `Get`) leaves it. -/
def kvNext (kind : w8) (key val : List w8) (m : KVMap) : KVMap :=
  if kind = opPutB then kvUpd m key val
  else if kind = opAppendB then kvUpd m key (m key ++ val)
  else m

/-- One datum of the client log applied to the store. -/
def kvApply (m : KVMap) (d : List w8) : KVMap :=
  match decodeOp d with
  | some (_, _, k, key, v) => kvNext k key v m
  | none => m

/-- A datum's key (the empty key for a datum that is no operation): what its operation
answers, the key's value after it. -/
def dkey (d : List w8) : List w8 :=
  match decodeOp d with
  | some (_, _, _, key, _) => key
  | none => []

/-- The store after the client log `L`. -/
def kvFold (L : List (List w8)) : KVMap := L.foldl kvApply kvEmpty

/-- `apply`'s table: the decodable data of the client log `L`, each mapped to `true`. -/
def AppliedOk (A : GMap (List w8) Bool) (L : List (List w8)) : Prop :=
  ∀ d, A !! d = if d ∈ L ∧ (decodeOp d).isSome then some true else none

theorem encodeOp_length (replica seq : w64) (kind : w8) (key val : List w8) :
    (encodeOp replica seq kind key val).length = 25 + key.length + val.length := by
  simp [encodeOp, u64Le_length]; omega

theorem decodeOp_encodeOp (replica seq : w64) (kind : w8) (key val : List w8)
    (hk : (key.length : Int) < 2 ^ 64) :
    decodeOp (encodeOp replica seq kind key val) = some (replica, seq, kind, key, val) := by
  have hr := u64Le_length replica
  have hs := u64Le_length seq
  have hn := u64Le_length (W64 key.length)
  have hkz : uint.Z (W64 key.length) = key.length := by word
  have hkn : uint.nat (W64 key.length) = key.length := by word
  have hA : (u64Le replica ++ u64Le seq ++ [kind]).length = 17 := by simp [u64Le_length]
  have h1 : (encodeOp replica seq kind key val).take 8 = u64Le replica := by
    simp [encodeOp, u64Le_length]
  have h2 : ((encodeOp replica seq kind key val).drop 8).take 8 = u64Le seq := by
    simp [encodeOp, u64Le_length]
  have h3 : (encodeOp replica seq kind key val).getD 16 (W8 0) = kind := by
    simp [encodeOp, List.getD_eq_getElem?_getD, List.getElem?_append_right, u64Le_length]
  have h4 : ((encodeOp replica seq kind key val).drop 17).take 8 = u64Le (W64 key.length) := by
    have : encodeOp replica seq kind key val =
        (u64Le replica ++ u64Le seq ++ [kind]) ++ (u64Le (W64 key.length) ++ (key ++ val)) := by
      simp [encodeOp]
    rw [this, List.drop_left' hA]
    exact List.take_left' (u64Le_length _)
  have h5 : (encodeOp replica seq kind key val).drop 25 = key ++ val := by
    have : encodeOp replica seq kind key val =
        (u64Le replica ++ u64Le seq ++ [kind] ++ u64Le (W64 key.length)) ++ (key ++ val) := by
      simp [encodeOp]
    rw [this, List.drop_left' (by simp [u64Le_length])]
  have hl := encodeOp_length replica seq kind key val
  unfold decodeOp
  rw [h4, u64Le_to_word, h5, hkn, hl, if_pos (by omega), if_pos (by rw [hkz]; push_cast; omega),
    h1, h2, h3, u64Le_to_word, u64Le_to_word, List.take_left' rfl, List.drop_left' rfl]

theorem opKey_encodeOp (replica seq : w64) (kind : w8) (key val : List w8)
    (hk : (key.length : Int) < 2 ^ 64) :
    opKey (encodeOp replica seq kind key val) = some (replica, seq) := by
  simp [opKey, decodeOp_encodeOp _ _ _ _ _ hk]

theorem kvFold_snoc (L : List (List w8)) (d : List w8) :
    kvFold (L ++ [d]) = kvApply (kvFold L) d := by
  simp [kvFold, List.foldl_append]

theorem kvApply_encodeOp (m : KVMap) (replica seq : w64) (kind : w8) (key val : List w8)
    (hk : (key.length : Int) < 2 ^ 64) :
    kvApply m (encodeOp replica seq kind key val) = kvNext kind key val m := by
  simp [kvApply, decodeOp_encodeOp _ _ _ _ _ hk]

theorem dkey_encodeOp (replica seq : w64) (kind : w8) (key val : List w8)
    (hk : (key.length : Int) < 2 ^ 64) :
    dkey (encodeOp replica seq kind key val) = key := by
  simp [dkey, decodeOp_encodeOp _ _ _ _ _ hk]

theorem kvApply_none (m : KVMap) (d : List w8) (h : decodeOp d = none) : kvApply m d = m := by
  simp [kvApply, h]

theorem kvUpd_same (m : KVMap) (k v : List w8) : kvUpd m k v k = v := by
  simp [kvUpd]

theorem kvUpd_other (m : KVMap) (k k' v : List w8) (h : k' ≠ k) : kvUpd m k v k' = m k' := by
  simp [kvUpd, h]

end EtcdGrove

end Perennial
