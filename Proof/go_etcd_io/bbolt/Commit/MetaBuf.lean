/-
`writeMeta`'s buffer (U10 of `notes/bbolt-proof-plan.md`): the page `tx.meta.Write` lays out in a
zeroed 4096-byte buffer (`metaBuf`): the header with id `txid % 2` and the meta flag, the meta
with its checksum, zeros after; its meta (`metaOf_metaBuf`), and no valid meta at
`getPageSize`'s probes (`metaBuf_probes`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.common

section metabuf
variable [GooseExts]

/-- The zero page header (a zeroed buffer's first 16 bytes). -/
def zeroHdr : Page := ⟨W64 0, W16 0, W16 0, W32 0⟩

-- `metaSummed` is in `Model/Meta` (batch 37).

/-- The header `Meta.Write` leaves in a zeroed buffer: id `txid % 2`, the meta flag. -/
def metaHdr (mv : Meta) : Page := { zeroHdr with id' := mv.txid' % W64 2, flags' := W16 4 }

/-- **`writeMeta`'s buffer**: the header, the summed meta, zeros. -/
def metaBuf (mv : Meta) : List w8 :=
  encode (metaHdr mv) ++ encode (metaSummed mv) ++ List.replicate 4016 (W8 0)

theorem metaBuf_length (mv : Meta) : (metaBuf mv).length = 4096 := by
  simp only [metaBuf, List.length_append, ByteEncoding.encode_length, List.length_replicate]

theorem metaOf_metaBuf (mv : Meta) : metaOf (metaBuf mv) = metaSummed mv := by
  unfold metaOf bytesAt metaBuf
  rw [List.append_assoc, List.drop_left' (ByteEncoding.encode_length _),
    List.take_left' (ByteEncoding.encode_length _), ByteEncoding.decode_encode]

theorem decode_zero_meta : (decode (List.replicate 64 (W8 0)) : Meta).magic' = W32 0 := rfl

theorem not_metaValid_zero (xs : List w8) (h : bytesAt xs 16 64 = List.replicate 64 (W8 0)) :
    ¬ metaValid (metaOf xs) := by
  unfold metaValid metaOf
  rw [h, decode_zero_meta]
  simp [boltMagic]

omit [GooseExts] in
theorem bytesAt_zeros (a b : List w8) (n k : Nat) (ha : a.length = 16) (hb : b.length = 64)
    (hk : 80 ≤ k) (hn : k + 80 ≤ 80 + n) :
    bytesAt ((a ++ b ++ List.replicate n (W8 0)).drop k) 16 64 = List.replicate 64 (W8 0) := by
  unfold bytesAt
  have hab : (a ++ b).length = 80 := by simp only [List.length_append, ha, hb]
  rw [List.drop_append, (List.drop_eq_nil_of_le (by omega) : List.drop k (a ++ b) = []), List.nil_append, hab,
    List.drop_replicate, List.drop_replicate, List.take_replicate]
  congr 1; omega

/-- No valid meta at offsets 1024 and 2048 of the buffer (zeros there). -/
theorem metaBuf_probes (mv : Meta) :
    ¬ metaValid (metaOf ((metaBuf mv).drop 1024)) ∧
      ¬ metaValid (metaOf ((metaBuf mv).drop 2048)) := by
  constructor <;> apply not_metaValid_zero <;> unfold metaBuf <;>
    exact bytesAt_zeros _ _ _ _ (ByteEncoding.encode_length _) (ByteEncoding.encode_length _)
      (by omega) (by omega)

end metabuf

end bbolt
end EtcdGrove
end Perennial
