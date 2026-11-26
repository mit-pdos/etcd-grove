/-
`writeMeta`'s buffer (U10 of `notes/bbolt-proof-plan.md`): the page `tx.meta.Write` lays out in a
zeroed 4096-byte buffer (`metaBuf`): the header with id `txid % 2` and the meta flag, the meta
with its checksum, zeros after; its meta (`metaOf_metaBuf`), and its zero tail (`metaBuf_tail`).
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

theorem metaBuf_drop80 (mv : Meta) : (metaBuf mv).drop 80 = List.replicate 4016 (W8 0) := by
  unfold metaBuf
  have hab : (encode (metaHdr mv) ++ encode (metaSummed mv)).length = 80 := by
    simp only [List.length_append, ByteEncoding.encode_length]
  rw [List.drop_append, (List.drop_eq_nil_of_le (by omega) :
    List.drop 80 (encode (metaHdr mv) ++ encode (metaSummed mv)) = []), List.nil_append, hab]
  rfl

/-- **The buffer's tail is zero** (its bytes after the header and the meta). -/
theorem metaBuf_tail (mv : Meta) : metaTailZero (metaBuf mv) := by
  unfold metaTailZero
  rw [metaBuf_drop80]
  intro b hb
  exact List.eq_of_mem_replicate hb

end metabuf

end bbolt
end EtcdGrove
end Perennial
