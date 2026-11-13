/-
`(*walpb.Snapshot).Clone()` (record.go:34-39): `&Snapshot{}` for a nil receiver, else
`proto.Clone(s).(*Snapshot)`. For a snapshot of index and term `s` (`walSnapIdTerm`, so non-nil),
a fresh one of the same index and term (`openAtIndex`'s `startSnap.Clone()`, S/wal.go:400). Proved
in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/Snapshot__Clone.lean`, over the
hypothesis `proto.CloneWalSnap.spec`. W5 of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PkgInit

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
abbrev go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.Clone.spec : Prop :=
  ∀ (sp : Loc) (s : w64 × w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal.walpb ∗
      walSnapIdTerm (GF := GF) sp s }}
    (App (Val (sp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty
      @!! go!"Clone")) (Val #()))
  {{ (sp' : Loc), RET #sp'; walSnapIdTerm sp' s }}

end spec

end EtcdGrove
end Perennial
