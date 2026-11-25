-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raft__hardState.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). -/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.RaftReadLend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.hardState()`: `pb.HardState{Term: r.Term, Vote: r.Vote, Commit:
r.raftLog.committed}`.

raft v3.7 (2026-10-15, stage R4): a fresh `&pb.HardState{Term: new(r.Term), ...}`, returned
read-only for good (`hsRO`, D4: shared by `Ready`, `prevHardSt` and the storage).

(2026-11-12, trace-check step 4) On the fields it reads only (`ownRaftCore`: `Term`, `Vote`,
`raftLog` and the log), so that `makeTracingState`, hence `traceEvent`, runs on raft's read view
(`RaftReadLend`) at `switchToConfig`'s hook, the struct open at its tracker; a caller holding the
whole struct takes the core out of it (`ownRaftPhysC_core`). Until then on `ownRaftPhysCV c c.voters`.

(2026-11-17, wal-link L1b, decided by etcd-grove-03) Canonical (`hsROC`: the three cells set, no unknown
fields), was `hsRO`: the WAL's state record is then a function of the model. -/
abbrev raft.hardState.spec : Prop :=
  ∀ (r : Loc) (id : w64) (s : NState),
  {{ ownRaftCore (GF := GF) r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hardState")) (Val #()))
  {{ (p : Loc), RET #p; hsROC p (hardstateVal (nodeHardstate s)) ∗ ownRaftCore r id s }}

end spec

end EtcdGrove
end Perennial
