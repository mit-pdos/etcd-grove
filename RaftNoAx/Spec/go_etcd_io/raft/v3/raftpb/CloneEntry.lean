/-
`raftpb.CloneEntry` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
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

/-- `CloneEntry(e)` (`raftpb/noax.go`, the fork's branch raft37-goose-lean-noax,
`notes/raft-noax.md`): what `proto.Clone` of a frozen message of a registered type was stated to do
(`Spec/google_golang_org/protobuf/proto/ClonePb.lean`), at the type `*pb.Entry`: a fresh `*Entry`
owned, at a content `c'` of the same wire content, whose unknown fields are valid, and which is
exactly `c` when `c`'s model marshals. -/
abbrev raftpb.CloneEntry.spec : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF I.data.ty = some I → I.data.ty = raftpb.Entry.ty →
  ∀ (l : Loc) (c : I.data.C),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ I.data.roC l c }}
    (App (Val #(functions raftpb.CloneEntry [])) (Val #l))
  {{ (l' : Loc), RET #l';
      ∃ c' : I.data.C, I.data.decC l' c' ∗
        ⌜I.data.eqv (I.data.modelOf c) (I.data.modelOf c') ∧ I.data.ufValid c' ∧
          (I.data.marshals (I.data.modelOf c) → c' = c)⌝ }}

end spec

end EtcdGrove
end Perennial
