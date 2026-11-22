-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/UnmarshalConfChangeV2.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.UnmarshalConfChangeV2` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`). Stated as the `proto` trust-boundary spec it replaces.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `UnmarshalConfChangeV2(d, cc)` (`raftpb/noax.go`, the fork's branch raft37-goose-lean-noax,
`notes/raft-noax.md`): what `proto.Unmarshal` into a `*pb.ConfChangeV2` was stated to do
(`Spec/google_golang_org/protobuf/proto/UnmarshalConfChangeV2.lean`): it computes `ccDecodeV2`; on
bytes it decodes, `nil` and the message holds the content, owned; on any other bytes a non-`nil`
error (`errDecodeConfChange`), the message some value. It never retains `d`. -/
abbrev raftpb.UnmarshalConfChangeV2.spec : Prop :=
  ∀ (d : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (x : raftpb.ConfChangeV2),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ d ↦*{dq} bs ∗ p ↦ x }}
    (App (App (Val #(functions raftpb.UnmarshalConfChangeV2 [])) (Val #d)) (Val #p))
  {{ (err : GoInterface), RET #err; d ↦*{dq} bs ∗
      match ccDecodeV2 bs with
      | some m => ⌜err = interface.nil⌝ ∗ ownConfChangeV2 p (DFrac.own 1) m
      | none => ⌜err ≠ interface.nil⌝ ∗ ∃ x' : raftpb.ConfChangeV2, p ↦ x' }}

end spec

end EtcdGrove
end Perennial
