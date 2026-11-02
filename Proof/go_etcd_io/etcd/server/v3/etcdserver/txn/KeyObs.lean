/-
**The writer's observation of the key bucket** (the merged snapshot's window, S2,
`etcdserver.mergedCreate_window`; `notes/decisions.md`, "The merged snapshot's window: the writer's
key observation"). Lean-first (no Rocq counterpart).

`kvWriter_keyObs`: the sole writer at the committed log `log`, with the batch lock's resource of a
real backend (`mvcc.lateW d.gx`, what `backend.Snapshot`'s observation gets as `W`) and a view of
the backend's data (`backend.viewAt`), sees the key bucket at most `bucketMap log`, and exactly
`bucketMap log` when the backend's store does not compact (`d.cm = false`). **Open** (a named
`sorry`): the writer does not yet hold a handle on the batch lock's log; M2's item 37 (the writer's
pin of `writerRes`'s log, `notes/m2-storage-plan.md`, "Task 4: item 37") proves it inside mvcc.

`kvWriter_noCmp` (open, the same item): with compaction off, a snapshot's data records no
compaction (the reader's bound `backend.fkRd` that `backend.Snapshot` gives, 2026-11-02).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Writer
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section keyObs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **(open) The writer's observation of the key bucket**: the sole writer of the store `(s, γ)`
over the real backend `d` at the log `log`, the backend's batch lock resource and a view `vd` of
its data: every key `vd` has is `bucketMap log`'s, at its value (thin, both modes: the compaction
deletes keys physically), and `vd` is `bucketMap log` on the key bucket when the store does not
compact. -/
theorem kvWriter_keyObs (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (log : mvcc.Log) (vd : backend.VData) :
    kvWriter (GF := GF) s γ log ∗ mvcc.lateW d.gx ∗ backend.viewAt d.γB vd ⊢
      ⌜(∀ k v, vd.lookup (mvcc.keyName, k) = some v → (mvcc.bucketMap log).lookup k = some v) ∧
        (d.cm = false → ∀ k, vd.lookup (mvcc.keyName, k) = (mvcc.bucketMap log).lookup k)⌝ := by
  sorry

/-- **(open) The writer's store records no compaction in a snapshot**: the sole writer of the store
`(s, γ)` over the real backend `d`, with a reader's lower bound of the backend's compaction-key flag
(`backend.fkRd`, what `backend.Snapshot` gives over the snapshot's data), knows the reader's state
has no compaction key when the store does not compact (`fkRd_abs`, with the off-mode store's
no-compaction token `bkNoCmp d.γB`, which item 37 lends the writer). -/
theorem kvWriter_noCmp (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (log : mvcc.Log) (rv : backend.RView) :
    kvWriter (GF := GF) s γ log ∗ backend.fkRd d.γB d.P rv ⊢
      ⌜d.cm = false → backend.fkAbsRv d.P rv⌝ ∗ kvWriter s γ log := by
  sorry

end keyObs

end txn
end EtcdGrove
end Perennial
