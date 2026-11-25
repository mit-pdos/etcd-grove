-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/appendVarint.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.appendVarint` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-codec.md`). A helper of the conf change codecs.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb
public import KvRaft.Proof.go_etcd_io.raft.v3.PbContentOwn
public import KvRaft.Proof.go_etcd_io.raft.v3.CCCodecLen

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

/-- `appendVarint(b, v)` (`raftpb/noax.go`): `b` with `v`'s minimal varint (`ccVarint`) appended. -/
abbrev raftpb.appendVarint.spec : Prop :=
  ∀ (b : GoSlice) (B : List w8) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      b ↦* B ∗ ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val #(functions raftpb.appendVarint [])) (Val #b)) (Val #v))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ ccVarint v) ∗ ownSliceCap w8 s (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
