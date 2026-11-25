-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/marshalConfChangeSingle.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.marshalConfChangeSingle` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-codec.md`). A helper of the conf change codecs.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb
public import KvRaft.Proof.go_etcd_io.raft.v3.PbContentOwn
public import KvRaft.Proof.go_etcd_io.raft.v3.CCWireRoundtrip

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

/-- `marshalConfChangeSingle(s)` (`raftpb/noax.go`) of a change of a `ConfChangeV2`'s list (non-`nil`, frozen, `ccsRoC`): a fresh slice containing its set fields and its preserved unknown fields. -/
abbrev raftpb.marshalConfChangeSingle.spec : Prop :=
  ∀ (p : Loc) (c : ConfChangeSingleM) (uf : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ccsRoC p c uf }}
    (App (Val #(functions raftpb.marshalConfChangeSingle [])) (Val #p))
  {{ (s : GoSlice) (bs : List w8), RET #s; s ↦* bs ∗ ⌜CCSingleWireEnc c uf bs⌝ }}

end spec

end EtcdGrove
end Perennial
