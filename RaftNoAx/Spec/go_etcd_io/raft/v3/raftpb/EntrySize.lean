/-
`raftpb.EntrySize` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`). Stated as the `proto` trust-boundary spec it replaces.
-/
module

public import RaftNoAx.Proof.google_golang_org.protobuf.proto.InvProto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `EntrySize(e)` (`raftpb/noax.go`, the fork's branch raft37-goose-lean-noax,
`notes/raft-noax.md`): what `proto.Size` of a frozen message of a registered type was stated to do
(`Spec/google_golang_org/protobuf/proto/SizePb.lean`), at the type `*pb.Entry`: if the content's
size (the instance's `size`) is below `2^63`, the result is it. -/
abbrev raftpb.EntrySize.spec : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF I.data.ty = some I → I.data.ty = raftpb.Entry.ty →
  ∀ (l : Loc) (c : I.data.C),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ I.data.roC l c }}
    (App (Val #(functions raftpb.EntrySize [])) (Val #l))
  {{ (n : w64), RET #n; ⌜I.data.size c < 2 ^ 63 → sint.Z n = I.data.size c⌝ }}

end spec

end EtcdGrove
end Perennial
