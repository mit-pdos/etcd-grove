/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__snapshot.lean`.
Lean-first (no Rocq counterpart; kvreconf-snapshot-thread, 2026-10-30).

The request's snapshot part gives `CreateSnapshot` all it takes (`snapReqOk`); either answer raises
what is known of the stored snapshot to the request's index (`memSnapLb`), and the `panic` on any
other error is unreachable. The compaction part is `maybeCompact`'s: `FirstIndex` is past the
request's compaction point `c`; the target `x = first + below(hi - first + 1)` is in `[first, hi]`,
`hi` the least of the request's bound and the known stored index, so its entry is frozen
(`frozenTo_at`), the node applied it (`nodeAppliedLb_mono`, the storage's `J.B`) and the stored
snapshot reaches it (`memSnapLb_mono`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Replica.snapshot.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Compact : MemoryStorage.Compact.spec (GF := GF) (hG := hG)) :
    Replica.snapshot.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end kvreconf
end EtcdGrove
end Perennial
