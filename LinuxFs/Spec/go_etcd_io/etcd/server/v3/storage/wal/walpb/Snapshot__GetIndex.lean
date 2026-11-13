/-
`e.GetIndex()` of a `*walpb.Snapshot` (record.pb.go, translated): the snapshot's index, of a frozen
snapshot (`walSnapAt`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/Snapshot__GetIndex.lean`.
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec : Prop :=
  ∀ (sp : Loc) (sm : SnapshotMetadataM) (cs : Bool),
  {{ walSnapAt (GF := GF) sp sm cs }}
    (App (Val (sp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty
      @!! go!"GetIndex")) (Val #()))
  {{ RET #sm.Index'; True }}

end spec

end EtcdGrove
end Perennial
