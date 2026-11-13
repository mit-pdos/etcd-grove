/-
`d.LastCRC()` (decoder.go:212): the CRC (`d.crc.Sum32()`). Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/decoder__LastCRC.lean`.
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.spec : Prop :=
  ∀ (d : Loc) (IoE : GoInterface → Prop) (eof : GoInterface) (fs : List (DecFile GF)) (off : Nat)
    (c : w32) (live : Bool),
  {{ ownDecoder d IoE eof fs off c live }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.decoder.ty @!! go!"LastCRC")) (Val #()))
  {{ RET #c; ownDecoder d IoE eof fs off c live }}

end spec

end EtcdGrove
end Perennial
