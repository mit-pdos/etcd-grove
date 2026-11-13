/-
`d.Decode(rec)` (decoder.go:81-86): `rec.Reset()`, then `decodeRecord` under `d.mu`: what
`goDecode` says, or an I/O error, or a failed `proto.Unmarshal` (`decPost`); `C` is the WAL's
codec `walCodec`. Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/decoder__Decode.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__decodeRecord

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
abbrev go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.spec : Prop :=
  ∀ (C : WalCodec) (d rp : Loc) (IoE : GoInterface → Prop) (eof ueof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (c : w32),
  C = walCodec →
  {{ decEnv IoE eof ueof ∗ ownDecoder d IoE eof fs off c true ∗ ownRecAny rp }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.decoder.ty @!! go!"Decode")) (Val #rp))
  {{ (err : GoInterface), RET #err; decPost C d rp IoE eof ueof fs off c err }}

end spec

end EtcdGrove
end Perennial
