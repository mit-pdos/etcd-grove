/-
`walpb.ValidateSnapshotForWrite(e)` (record.go:45-56, translated) of a frozen snapshot (`walSnapAt`)
whose conf state is non-nil unless its index is 0: `nil` (its `Term` and `Index` pointers are
non-nil, `walSnapAt`'s content). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/ValidateSnapshotForWrite.lean`.
W4 of `notes/wal-fsext-plan.md` (`SaveSnapshot`'s callee); Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Defs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite.spec : Prop :=
  ∀ (Mr : WalEnc.WalMarshal) (sp : Loc) (sm : SnapshotMetadataM) (cs : Bool),
  (sm.Index' = W64 0 ∨ cs = true) →
  {{ walSnapAt (GF := GF) Mr sp sm cs }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite)) (Val #sp))
  {{ RET #GoInterface.nil; True }}

end spec

end EtcdGrove
end Perennial
