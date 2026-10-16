/-
`proto.Clone` of a raft v3.7 `*pb.Snapshot`: the trust boundary, stage R1. Raft and
`MemoryStorage` clone a snapshot on every path into and out of the log and the storage
(`log.go:295`, `log_unstable.go:114,196`, `storage.go:213,234,262`).
Lean-first; stated over the raftpb ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean`
(a raft v3.7 statement about `proto.*`, kept apart from the etcd side's `Clone.lean`, `Size.lean`,
`Marshal.lean`, `Unmarshal.lean`, as `MarshalIRR.lean` is from `Marshal.lean`; until stage R6 swapped
the raft trees, 2026-10-16, this file was the only one importing the `Raft37` tree's raftpb).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `proto.Clone(s)` of a `*pb.Snapshot` holding `s` (at any fraction): a fresh `*pb.Snapshot`
holding `s`, owned, its metadata and conf state fresh too (a deep copy); of a nil `*pb.Snapshot`
(an invalid message), a nil `*pb.Snapshot`.

Against protobuf-go v1.36.11: `Clone` merges into a new message, recursively for message fields
(`mergeMessage` allocates the destination's `Metadata`, then its `ConfState`), copying bytes
(`Data`) and repeated scalars (the conf state's lists: `append` onto the empty destination) and
the unknown fields; it only reads the source. "If the top-level message is invalid, it returns
an invalid message as well" (`proto.Clone`'s documentation): `Clone((*Snapshot)(nil))` is a
typed nil. -/
abbrev proto.CloneSnapshot.spec : Prop :=
  (∀ (p : Loc) (dq : DFrac) (s : SnapshotM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ ownSnapM p dq s }}
      (App (Val (@! google_golang_org.protobuf.proto.Clone)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.Snapshot.ty) #p)))
    {{ (p' : Loc), RET #(interface.mkOk (go.GoType.PointerType raftpb.Snapshot.ty) #p');
        ownSnapM p dq s ∗ ownSnapM p' (DFrac.own 1) s }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.Snapshot.ty) #(null : Loc))))
  {{ RET #(interface.mkOk (go.GoType.PointerType raftpb.Snapshot.ty) #(null : Loc)); True }}

end spec

end EtcdGrove
end Perennial
