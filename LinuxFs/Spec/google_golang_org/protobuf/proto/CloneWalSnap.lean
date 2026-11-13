/-
`proto.Clone` of a `*walpb.Snapshot` (`walpb.Snapshot.Clone`, record.go:34-39): **a hypothesis** of
`Snapshot.Clone`'s proof, not proved here and not an axiom. The clone is a fresh message with the
same index and term (and a conf state iff the original has one), which the caller may freeze
(`walSnapIdTerm`, persistent).

What it stands for: `proto.ClonePb.spec` (the main tree's per-type trust boundary, over a registered
message type, `pbModelOf`) at `walpb.Snapshot`, once that type is registered in the part (as
`walpb.Record` is, `PbRecord.lean`), with `walSnapAt` over its content model: W6's `SaveSnapshot`
fix (`walSnapAt` with the full protobuf content model, `notes/wal-fsext-plan.md`) brings both; this
statement then follows from `ClonePb` (the clone's model equals the original's, so its index and
term). Until then it is a hypothesis, recorded in the W3/W5 log. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit

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

/-- See the file header. -/
abbrev proto.CloneWalSnap.spec : Prop :=
  ∀ (sp : Loc) (s : w64 × w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ walSnapIdTerm sp s }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty) #sp)))
  {{ (sp' : Loc), RET #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty) #sp');
      walSnapIdTerm sp' s }}

end spec

end EtcdGrove
end Perennial
