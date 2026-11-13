/-
`newEncoder(w, prevCrc, pageOffset)` (`server/storage/wal/encoder.go:47-55`): an encoder over the
stream writer `wi`, its CRC at `prevCrc` (over the WAL's Castagnoli table `crcTable`), nothing
pending, its page writer at `pageOffset` (`walPageBytes`-aligned pages); premise `0 ≤ pageOffset <
2^62` (`ioutil.NewPageWriter`'s). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/newEncoder.lean`. W6; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.EncDefs

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

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.newEncoder.spec : Prop :=
  ∀ (wi : GoInterfaceOk) (prev : w32) (off : w64),
  0 ≤ sint.Z off → sint.Z off < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil ∗ walCrcTable }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.newEncoder))
      (Val #(GoInterface.ok wi))) (Val #prev)) (Val #off))
  {{ (e : Loc), RET #e; ownEncoder e wi prev [] }}

end spec

end EtcdGrove
end Perennial
