/- Lean-first (no Rocq counterpart).

# Meta slots on raw bytes, for the crash proof

What the crash premise (`Crash/Premise.lean`) says of a meta slot is stated on its raw bytes
(`boltMetaValidates`, the first 56 bytes "as of one change"); bbolt's model reads a slot as
`metaOf` (`Model/Meta.lean`). This file connects the two:
* `metaValid_validates`: a valid decoded meta's raw bytes validate;
* `meta_eq_of_take`: two metas with the same first 56 bytes and the same checksum are one (so two
  *valid* ones with the same first 56 bytes are one, `meta_eq_of_valid`);
* `metaPre`: what bbolt's metas say of a slot whatever its checksum (magic and version right ⇒ page
  size 4096 and txid below a bound), the fact the crash invariant keeps of the slot a commit writes:
  the premise fixes only the first 56 bytes, so a torn checksum may validate an old slot's 56 bytes.
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Premise
public import Proof.go_etcd_io.bbolt.Model.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.common

section metas
variable [GooseExts]

theorem leNat_eq (l : List w8) : leNat l = bytesNat l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [leNat, List.foldr_cons] at ih ⊢; rw [ih]; rfl

theorem decode_w32_toNat (l : List w8) (h : l.length = 4) :
    (decode l : w32).toNat = bytesNat l := by
  rw [decode_w32, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := bytesNat_lt l; rw [h] at this; exact Nat.lt_of_lt_of_le this (by decide)

theorem decode_w64_toNat (l : List w8) (h : l.length = 8) :
    (decode l : w64).toNat = bytesNat l := by
  rw [decode_w64, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := bytesNat_lt l; rw [h] at this; exact Nat.lt_of_lt_of_le this (by decide)

theorem decode_meta_magic (r : List w8) : (decode r : Meta).magic' = decode (r.take 4) := rfl

theorem decode_meta_version (r : List w8) :
    (decode r : Meta).version' = decode ((r.drop 4).take 4) := rfl

theorem decode_meta_checksum (r : List w8) :
    (decode r : Meta).checksum' = decode (r.drop 56) := by
  show (decode ((((((((r.drop 4).drop 4).drop 4).drop 4).drop 16).drop 8).drop 8).drop 8) : w64) = _
  simp only [List.drop_drop]

/-- A meta's bytes: its first 56, then its checksum's. -/
theorem encode_meta_split (m : Meta) : encode m = (encode m).take 56 ++ encode m.checksum' := by
  show encode (m.magic', m.version', m.pageSize', m.flags', m.root', m.freelist', m.pgid',
      m.txid', m.checksum') = List.take 56 (encode (m.magic', m.version', m.pageSize', m.flags',
      m.root', m.freelist', m.pgid', m.txid', m.checksum')) ++ encode m.checksum'
  simp only [ByteEncoding.prod_encode, ← List.append_assoc]
  rw [List.take_left' (by simp)]

/-- **Two metas with the same first 56 bytes and checksum are one.** -/
theorem meta_eq_of_take (m1 m2 : Meta) (h : (encode m1).take 56 = (encode m2).take 56)
    (hc : m1.checksum' = m2.checksum') : m1 = m2 := by
  apply ByteEncoding.encode_inj
  have e1 := encode_meta_split m1
  have e2 := encode_meta_split m2
  rw [e1, e2, h, hc]

/-- The checksum a meta's first 56 bytes call for. -/
theorem metaSum_take (m : Meta) : metaSum m = fnv64a ((encode m).take 56) := rfl

/-- **Two valid metas with the same first 56 bytes are one.** -/
theorem meta_eq_of_valid (m1 m2 : Meta) (h : (encode m1).take 56 = (encode m2).take 56)
    (h1 : metaValid m1) (h2 : metaValid m2) : m1 = m2 :=
  meta_eq_of_take m1 m2 h (by rw [h1.2.2, h2.2.2, metaSum_take, metaSum_take, h])

/-- A meta with the first 56 bytes of `m` has `m`'s fields but the checksum. -/
theorem meta_with_of_take (m1 m2 : Meta) (h : (encode m1).take 56 = (encode m2).take 56) :
    m1 = { m2 with checksum' := m1.checksum' } := by
  refine meta_eq_of_take _ _ ?_ rfl
  rw [h]
  -- the first 56 bytes do not depend on the checksum
  show List.take 56 (encode (m2.magic', m2.version', m2.pageSize', m2.flags', m2.root',
      m2.freelist', m2.pgid', m2.txid', m2.checksum')) = List.take 56 (encode (m2.magic',
      m2.version', m2.pageSize', m2.flags', m2.root', m2.freelist', m2.pgid', m2.txid',
      m1.checksum'))
  simp only [ByteEncoding.prod_encode, ← List.append_assoc]
  rw [List.take_left' (by simp), List.take_left' (by simp)]

/-- **A valid decoded meta's raw bytes validate** (`boltMetaValidates`, the premise's check). -/
theorem metaValid_validates (r : List w8) (hl : r.length = 64) (hv : metaValid (decode r : Meta)) :
    boltMetaValidates r := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · rw [leNat_eq, ← decode_w32_toNat _ (by simp [hl]), ← decode_meta_magic, h1]; rfl
  · rw [leNat_eq, ← decode_w32_toNat _ (by simp [hl]), ← decode_meta_version, h2]; rfl
  · rw [leNat_eq, ← decode_w64_toNat _ (by simp [hl]), ← decode_meta_checksum, h3, metaSum_take,
      ByteEncoding.encode_decode r hl]
    rfl

/-- **What a slot whose first 56 bytes are a meta's says, whatever its checksum**: if its magic and
version are right, its page size is 4096 and its txid below `T`. -/
def metaPre (m : Meta) (T : Nat) : Prop :=
  m.magic'.toNat = boltMagic → m.version'.toNat = boltVersion →
    m.pageSize'.toNat = 4096 ∧ m.txid'.toNat < T

/-- `metaPre` depends on the first 56 bytes only. -/
theorem metaPre_of_take {m1 m2 : Meta} {T : Nat} (h : (encode m1).take 56 = (encode m2).take 56)
    (hp : metaPre m2 T) : metaPre m1 T := by
  rw [meta_with_of_take m1 m2 h]; exact hp

/-- A valid meta of page size 4096 and txid below `T` is `metaPre`. -/
theorem metaPre_of_valid {m : Meta} {T : Nat} (hps : m.pageSize'.toNat = 4096)
    (ht : m.txid'.toNat < T) : metaPre m T := fun _ _ => ⟨hps, ht⟩

theorem metaPre_mono {m : Meta} {T T' : Nat} (h : metaPre m T) (hT : T ≤ T') : metaPre m T' :=
  fun h1 h2 => let ⟨a, b⟩ := h h1 h2; ⟨a, Nat.lt_of_lt_of_le b hT⟩

end metas

end bbolt
end EtcdGrove
end Perennial
