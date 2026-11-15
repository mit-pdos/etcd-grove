/-
**What step 4 of `srvSnapApplied_of_walk` reads off the restored log** (D22 receiver epochs, S8d,
`SnapApplyKV.lean`): the restored state's leases (none) from the log's puts carrying none. (Strict
M1, 2026-11-06: over `LogNoLease` of the image's history, `SnapImageFacts.nolease`; until then
`restoreLogOk`'s third conjunct, with the sole writer's log facts, `soleLog`.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreChunks

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **No lease is needed of a state whose history puts none, at any live set** (`leasesKnown L`;
`lean`'s `leasesKnown_restore`, over `LogNoLease` in place of `restoreLogOk`: R4, 2026-11-07, the
restored image's history attaches no lease to a key, whatever the lessor's live set `Recover`
restored). -/
theorem leasesKnown_noLease (L : List w64) (log : mvcc.Log) (h : mvcc.LogNoLease log) :
    ⊢ txn.leasesKnown (GF := GF) L (mvcc.stateAfter log) := by
  have hz := mvcc.stateAfter_leaseZero _ h
  unfold txn.leasesKnown txn.leasesOk
  iintro !> %l %hl
  iunfold txn.leaseOk
  ipureintro
  left
  obtain ⟨kv, hkv, rfl⟩ := List.mem_map.1 hl
  exact hz kv hkv

/-- **A state whose leased keys' leases are among `L` needs no other lease** (`leasesKnown L`; auth-lease
S3a, Draft rev 5 §5: the restored image's keys attach only leases `Recover` restored). -/
theorem leasesKnown_of_items (L : List w64) (log : mvcc.Log)
    (h : ∀ (k : GoString) (id : w64), mvcc.leaseItemsOf (mvcc.stateAfter log) !! ⟨k⟩ = some id → id ∈ L) :
    ⊢ txn.leasesKnown (GF := GF) L (mvcc.stateAfter log) := by
  unfold txn.leasesKnown txn.leasesOk
  iintro !> %l %hl
  iunfold txn.leaseOk
  ipureintro
  obtain ⟨kv, hkv, rfl⟩ := List.mem_map.1 hl
  by_cases h0 : kv.lease = W64 0
  · left; exact h0
  · right
    apply h kv.key
    have hf := txn.findKey_of_mem_sorted (mvcc.stateAfter_sorted log) hkv
    show ((mvcc.findKey kv.key (mvcc.stateAfter log)).bind mvcc.kvLease) = some kv.lease
    rw [hf]; simp only [Option.bind_some, mvcc.kvLease]; rw [if_neg h0]

end proof

end EtcdGrove
end Perennial
