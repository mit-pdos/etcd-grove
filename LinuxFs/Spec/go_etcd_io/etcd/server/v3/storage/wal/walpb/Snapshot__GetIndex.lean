/-
`snap.GetIndex()` (record.pb.go, translated) of a frozen `*walpb.Snapshot` (`walSnapIdTerm`,
`WalDisk.lean`): its index. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/Snapshot__GetIndex.lean`. W5 of
`notes/wal-fsext-plan.md` (`selectWALFiles`); Lean-first.
-/
module

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
  ∀ (sp : Loc) (s : w64 × w64),
  {{ walSnapIdTerm (GF := GF) sp s }}
    (App (Val (sp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty @!! go!"GetIndex")) (Val #()))
  {{ RET #s.1; True }}

end spec

end EtcdGrove
end Perennial
