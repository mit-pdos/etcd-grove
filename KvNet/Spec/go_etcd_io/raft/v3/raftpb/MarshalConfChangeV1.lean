-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/MarshalConfChangeV1.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.MarshalConfChangeV1` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`). Stated as the `proto` trust-boundary spec it replaces.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvPb
public import KvNet.Proof.go_etcd_io.raft.v3.PbContentOwn

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

/-- `MarshalConfChangeV1(cc)` (`raftpb/noax.go`, the fork's branch raft37-goose-lean-noax,
`notes/raft-noax.md`): what `proto.Marshal` of a `*pb.ConfChange` was stated to do
(`Spec/google_golang_org/protobuf/proto/MarshalConfChange.lean`), without the error result: a fresh
slice of bytes that decode back to `m` (`ccDecodeV1`, `CCModel.lean`), of length at most
`ccLenMax`; the message untouched. -/
abbrev raftpb.MarshalConfChangeV1.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : ConfChangeM) (uf : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      ccPtsCC (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p) dq (.v1 m uf) }}
    (App (Val #(functions raftpb.MarshalConfChangeV1 [])) (Val #p))
  {{ (d : GoSlice) (bs : List w8), RET #d;
      ccPtsCC (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p) dq (.v1 m uf) ∗
      d ↦* bs ∗
      ⌜ccDecodeV1 bs = some m ∧
        (ccSize (.v1 m uf) + 64 < 2 ^ 63 → bs.length ≤ ccLenMax (.v1 m uf))⌝ }}

end spec

end EtcdGrove
end Perennial
