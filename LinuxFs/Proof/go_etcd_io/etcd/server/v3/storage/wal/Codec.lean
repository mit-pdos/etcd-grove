/-
**The WAL's codec, concretely** (`WalEnc.WalCodec`, `Proof/go_etcd_io/etcd/server/v3/storage/WalEncDecode.lean`):
CRC-32C (`hash.crc32.crc32c`, the model of `crc32.Update` over the Castagnoli table,
`LinuxFs/Spec/hash/crc32/Model.lean`), the record bytes the WAL's encoder writes (`WalEnc.walRecEnc`,
the transparent wire format of `walpb.Record` at the content `recOf r`) and `proto.Unmarshal`'s view
(`recDecode`, the registered `walpb.Record`'s `wire`, `PbRecord.lean`). Its laws (`walCodec_ok`)
are proved: `dec_enc` from the record type's encoder axiom `recEncC_ok`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PbRecord
public import LinuxFs.Spec.hash.crc32.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open WalEnc

/-- **The WAL's codec.** -/
def walCodec : WalCodec where
  crc32c := hash.crc32.crc32c
  encRec := walRecEnc
  decRec := recDecode

/-- **The codec's laws**: `dec_enc` from the record type's encoder axiom `recEncC_ok` (the WAL's
records have no unknown fields, and a record that fits a frame is far below `2^63` bytes). -/
theorem walCodec_ok : walCodec.Ok where
  dec_enc r h := by
    show recDecode (recEnc (recOf r)) = some r
    have hs : recSize (recOf r) < 2 ^ 63 := by
      have : (walCodec.encRec r).length = recSize (recOf r) := recEnc_length (recOf r)
      omega
    rw [recEncC_ok (recOf r) (by rw [recOf_uf]; exact ufWire.nil) hs, recOf_model]
  enc_ne r := walRecEnc_ne r
  crc_nil c := hash.crc32.crc32c_nil c

end EtcdGrove
end Perennial
