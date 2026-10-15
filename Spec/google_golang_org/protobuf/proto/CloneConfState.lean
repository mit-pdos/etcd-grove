/-
`proto.Clone` of a raft v3.7 `*pb.ConfState`: the trust boundary, stage R1. `ConfState.Equivalent`
clones both sides before sorting them (`raftpb/confstate.go:31-32`); `MemoryStorage.CreateSnapshot`
clones the conf state it is given (`storage.go:259`).
Lean-first; stated over the raftpb ownership predicates of `Raft37/Proof/go_etcd_io/raft/v3/InvPb.lean`
(this file imports only `Raft37` modules: the old raft's and `EtcdDeps`'s raftpb define the same
names). Until the raft trees are swapped (stage R6) a raft v3.7 statement about `proto.*` is kept
apart from the etcd side's (`Clone.lean`, `Size.lean`, `Marshal.lean`, `Unmarshal.lean`), as
`MarshalIRR.lean` is from `Marshal.lean`.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `proto.Clone(cs)` of a `*pb.ConfState` holding `c` (at any fraction): a fresh `*pb.ConfState`
holding `c`, owned; of a nil `*pb.ConfState`, a nil one.

Against protobuf-go v1.36.11: the four repeated `uint64` fields are copied into fresh slices
(`mergeUint64Slice`: `append` onto the empty destination's), `AutoLeave` into a fresh cell when
set (`nil` stays `nil`; either reads as `c.AutoLeave'`), the unknown fields copied (none, as
`csPts` requires of a conf state); the source is only read. -/
abbrev proto.CloneConfState.spec : Prop :=
  (∀ (p : Loc) (dq : DFrac) (c : ConfStateM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ ownCSM p dq c }}
      (App (Val (@! google_golang_org.protobuf.proto.Clone)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #p)))
    {{ (p' : Loc), RET #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #p');
        ownCSM p dq c ∗ ownCSM p' (DFrac.own 1) c }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #(null : Loc))))
  {{ RET #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #(null : Loc)); True }}

end spec

end EtcdGrove
end Perennial
