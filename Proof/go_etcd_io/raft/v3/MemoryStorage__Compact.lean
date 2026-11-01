/- `MemoryStorage.Compact` (`storage.go:271`; U8 v2 step 3). At or below the compaction point:
`ErrCompacted`, the lock's compaction point and its registration giving `memCompacted`. Past it, the
caller's frozen entry at `x` is in the map, so below the end (no panic), and is the physical entry
there (`MemOk`), numbered `x`: the new dummy is the caller's frozen entry; the map and the end are
unchanged, the compaction point moves to `x` (registered with `J.B x`). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.Compact.wp_proof
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Compact.spec (GF := GF) (hG := hG) := by
  sorry -- durability stage I (I-5): statement changed (mode o / detached memStorFresh c sv)

end proof

end EtcdGrove
end Perennial
