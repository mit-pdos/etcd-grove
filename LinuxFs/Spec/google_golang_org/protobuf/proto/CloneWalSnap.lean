/-
`proto.Clone` of a `*walpb.Snapshot` (`walpb.Snapshot.Clone`, record.go:34-39): **a hypothesis** of
`Snapshot.Clone`'s proof, not proved here and not an axiom. The clone is a fresh message with the
same index and term (and a conf state iff the original has one), which the caller may freeze
(`walSnapIdTerm`, persistent).

What it stands for: `proto.ClonePb.spec` (the main tree's per-type trust boundary, over a registered
message type, `pbModelOf`) at `walpb.Snapshot`, registered in the part since W6 (`pbSnapC`,
`walpb/PbSnapshot.lean`): the clone is `snapOwnC` at the original's content, which the caller freezes
(a lemma to write: `snapOwnC` to `snapRoC`, allocating the hidden fields' invariants). Until the part
has a copy of `ClonePb` and that lemma it is a hypothesis, recorded in the W3/W5 log. Lean-first.
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
