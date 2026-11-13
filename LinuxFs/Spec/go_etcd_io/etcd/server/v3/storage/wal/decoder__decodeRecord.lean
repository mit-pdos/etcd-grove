/-
`d.decodeRecord(rec)` (decoder.go:88-158, with the local fork fix: a failed `FileInfo` of the
file reached is returned) into a zero `*walpb.Record`, on the live decoder `(fs, off, c)`: what
`goDecode` says, or an I/O error, or a failed `proto.Unmarshal` (`decPost`). `C` is the WAL's
codec `walCodec`: CRC-32C (the trusted model's `crc32c`) and `proto.Unmarshal` of a record
(`proto.UnmarshalWalRecord.spec`: on success the canonical decoding `recDecode`; it may fail on
bytes that are no record's encoding). Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/decoder__decodeRecord.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.decoder.decodeRecord.spec : Prop :=
  ∀ (C : WalCodec) (d rp : Loc) (IoE : GoInterface → Prop) (eof ueof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (c : w32),
  C = walCodec →
  {{ decEnv IoE eof ueof ∗ ownDecoder d IoE eof fs off c true ∗
      (pbRecordC (GF := GF)).data.blank rp }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.decoder.ty @!! go!"decodeRecord")) (Val #rp))
  {{ (err : GoInterface), RET #err; decPost C d rp IoE eof ueof fs off c err }}

end spec

end EtcdGrove
end Perennial
