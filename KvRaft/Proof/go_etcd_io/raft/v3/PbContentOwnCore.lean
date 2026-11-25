-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/PbContentOwnCore.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The declarations `entPtsCC` of `Proof/go_etcd_io/raft/v3/PbContentOwn.lean`, split from it so that
the WAL (`Proof/go_etcd_io/etcd/server/v3/storage/wal/`) imports them without the rest (until
2026-11-15 an extract of `etc/gen-part-copies.py` for the part `LinuxFs/`;
notes/wal-lean-integration.md). The source imports this module.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.PbContentCore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section extract
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A `*Entry` at `dq` holding exactly the content `c`** (raft-entsize §2: `entPts`'s content
form; `entRoC` is its `discard` instance up to the fraction's form). -/
def entPtsCC (l : Loc) (dq : DFrac) (c : EntryC) : IProp GF :=
  iprop(∃ (pt pi pty : Loc) (ds : GoSlice),
    ⌜l ≠ null⌝ ∗
    l.[raftpb.Entry, go!"Term"] ↦{dq} pt ∗ optCell pt c.term ∗
    l.[raftpb.Entry, go!"Index"] ↦{dq} pi ∗ optCell pi c.index ∗
    l.[raftpb.Entry, go!"Type"] ↦{dq} pty ∗ optCell pty c.type ∗
    l.[raftpb.Entry, go!"Data"] ↦{dq} ds ∗ bytesC ds c.data ∗
    pbMsg raftpb.Entry l c.uf)

end extract

end EtcdGrove
end Perennial
