-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/appendBytes.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.appendBytes` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-codec.md`). A helper of the conf change codecs.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvPb
public import KvNet.Proof.go_etcd_io.raft.v3.PbContentOwn
public import KvNet.Proof.go_etcd_io.raft.v3.CCCodecLen

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

/-- `appendBytes(b, v)` (`raftpb/noax.go`): `b` with `v`'s length-delimited encoding (`ccBytesEnc`) appended; `v` untouched. -/
abbrev raftpb.appendBytes.spec : Prop :=
  ∀ (b : GoSlice) (B : List w8) (v : GoSlice) (dq : DFrac) (vs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      b ↦* B ∗ ownSliceCap w8 b (DFrac.own 1) ∗ v ↦*{dq} vs }}
    (App (App (Val #(functions raftpb.appendBytes [])) (Val #b)) (Val #v))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ ccBytesEnc vs) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      v ↦*{dq} vs }}

end spec

end EtcdGrove
end Perennial
