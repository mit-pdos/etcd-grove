/-
Lean-first (no Rocq counterpart). Trace-check's layer D (the harness, 2026-11-12;
`notes/trace-check-design.md` §2.3).

`(*Cluster).handleReady(r, rd)` (`examples/raft/tracecheck/concurrent.go`) for a `Ready` without a
snapshot (the `app` refutes one first: no snapshot is ever made, `tcSnapsInv`): it appends the
`Ready`'s entries to the replica's `MemoryStorage` (the `Ready`'s `appendRight`; their last index at
most `2^61`), persists its hard state, and applies its committed entries `ce` (after the delivered
log `D`) in order: a `ConfChange` (only the bootstrap log's `AddNode`s: `tcOps_v1_boot`) through
`node.ApplyConfChange` at the voters' membership, which it leaves as it is; a `ConfChangeV2` is
refuted (an empty one, `tcOps_emptyV2`, is committed only at a joint configuration,
`committed_emptyV2_joint`, and the view's is the voters' simple one). It returns the receipt
`Advance` takes (`advReceipt`, nothing frozen) and the view at `D ++ ce` (`ViewOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.HarnessDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [MemStorReg GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

attribute [local instance] memStorageModel

/-- See the file header. -/
abbrev Cluster.handleReady.spec : Prop :=
  ∀ (c : Loc) (W : TcW) (r n ms : Loc) (γs : MemStorNames) (id : w64) (rd : Ready)
    (D ce : List LogEntry) (es : List EntryM) (h hs0 : HardStateM) (v : ConfigView),
  ViewOk D v →
  (∀ e0, es.head? = some e0 →
    (∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = uint.nat e0.Index' + j) ∧
    uint.nat e0.Index' + es.length ≤ 2 ^ 61) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      tcWorld c W ∗ repInfo W.cl r id n ms γs ∗ repOwn r ∗ memStorMeta ms γs hs0 ∗
      committedEntriesAt rd.CommittedEntries' D.length ce ∗ isCommittedLogLb W.cl (D ++ ce) ∗
      deliveredLogLb n W.cl tcRaftN (D ++ ce) ∗ entsRO rd.Entries' es ∗ hsOpt rd.HardState' h ∗
      ⌜rd.Snapshot' = null⌝ ∗ appendRight (memStorIface ms) es ∗
      nodeConfig n W.cl tcRaftN v ∗ nodeRunning n W.cl tcRaftN 1 }}
    (App (App (Val (c @!! go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster.ty @!! go!"handleReady"))
      (Val #r)) (Val #rd))
  {{ RET #(); repOwn r ∗ ∃ (hs1 : HardStateM) (v' : ConfigView), memStorMeta ms γs hs1 ∗
      advReceipt (memStorIface ms) (D ++ ce).length es none ∗ nodeConfig n W.cl tcRaftN v' ∗
      nodeRunning n W.cl tcRaftN 1 ∗ ⌜ViewOk (D ++ ce) v'⌝ }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
