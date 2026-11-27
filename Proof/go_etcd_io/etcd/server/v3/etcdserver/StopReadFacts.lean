/- Lean-first (no Rocq counterpart).

# The stopped records' read facts (2026-11-27, the restart axiom's review R2)

The restart's `bootstrap` contract (`bootstrapRestartContract`, `InvRestart.lean`) takes the WAL interface's
read facts I1-I4 of the records the stopped member's files hold (`walReadFacts`, `WalApi.lean`) as a premise:
Go's `ReadAll` checks I3 (commit ≤ last) nowhere, and files whose WAL got a later `Save` past its last entry
make raft's `RestartNode` panic (`notes/axiom-review/bootstrap-restart-walreadfacts.md`). A graceful stop
gives them (`stop_cleanup_image`, `StopShutdown.lean`):
* I1 (entries consecutive from the base) and I4 (the snapshot record at the base): of the files' read
  (`walFiles_readShape`, `storage/WalRecs.lean`);
* I3 (base ≤ commit ≤ last): the records hold the node's durable state `S` (`StorageHolds`: their commit at
  most `S`'s, their entries `S`'s from their base) and raft's durable log reaches `S`'s commit
  (`raftState_logView`), so the records' last index is `S`'s and at least their commit;
* I2 (the last index within raft's room, `≤ 2^61 - 1`): `S`'s last index is, by **the interim law**
  `raftStateLastFits.law` (below): a node's durable log ends within its cluster's room (`readyFits`: the
  receipts' bound past the bootstrap log at most `2^61`), as every index raft hands out (`readyFits`'
  docstring, `lastRec_receipt`). Interim: raft's proof has the facts (each record past the bootstrap log
  keeps a time receipt) but no law of `raftState` states it yet; the linking module passes the axiom
  `raftStateLastFits_law_holds` (`raftStateLastFits.lean`).

A defs module: the law's statement and the pure composition.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi
public import Proof.go_etcd_io.raft.v3.DurableLogView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- **The stopped records' read facts, composed** (pure): from `StorageHolds S σ`, the read's shape (I1,
I4), raft's durable log reaching `S`'s commit (`raftState_logView`'s) and `S`'s last index within raft's
room. -/
theorem walReadFacts_of_stop (S : RaftState) (σ : StorContents) (fp : List EntryM)
    (hS : StorageHolds S σ)
    (hshape : walEntsWf σ ∧ ((σ.snap = none ∧ σ.base = entryID.mk (W64 0) (W64 0)) ∨
        ∃ m, σ.snap = some (SnapshotM.mk [] m) ∧ σ.base = entryID.mk m.Term' m.Index'))
    (hfull : (fp.length : Int) = uint.Z S.base.index')
    (hcommit : uint.nat S.commit ≤ (fp ++ S.ents).length)
    (hlast : S.last ≤ 2 ^ 61 - 1) :
    walReadFacts σ := by
  obtain ⟨hb, -, hents, -, -, hbc, -, hcS, -, -⟩ := hS
  have hlen : σ.ents.length = S.ents.length - (uint.Z σ.base.index' - uint.Z S.base.index').toNat := by
    rw [hents]; unfold RaftState.entsFrom; rw [List.length_drop]
  have hfl : fp.length = uint.nat S.base.index' := by
    have := hfull; omega
  simp only [List.length_append] at hcommit
  have hσlast : σ.last = S.last := by
    unfold StorContents.last RaftState.last StorContents.b
    unfold StorContents.b StorContents.commit at hbc
    unfold StorContents.commit at hcS
    rw [hlen]
    omega
  refine ⟨hshape.1, by rw [hσlast]; exact hlast, hbc, ?_, hshape.2⟩
  rw [hσlast]
  unfold RaftState.last
  unfold StorContents.commit at hcS
  omega

section law
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **The interim law: a node's durable log ends within its cluster's room** (see the file header):
in a cluster that fits (`readyFits`: the receipts' bound past the bootstrap log at most `2^61`), a
node's durable state's last index is at most `2^61 - 1`. -/
abbrev raftStateLastFits.law : Prop :=
  ∀ (cl : Cluster) (N : Namespace) (id : w64) (S : RaftState),
    isCluster (GF := GF) cl N ∗ readyFits cl N ∗ raftState cl id S ⊢ |={⊤}=>
      raftState cl id S ∗ ⌜S.last ≤ 2 ^ 61 - 1⌝

end law

end EtcdGrove
end Perennial

end
