/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreNC
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `NewStore` over a backend holding an image (B3, mvccfull's Freeze, 2026-11-10): the proof is
`NewStoreR.lean`'s (the resumed compaction inside `restore()` is a callee, `compactLockfree`). -/
theorem mvcc.NewStore.wp_proof
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewIdx : mvcc.newTreeIndex.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hHash : mvcc.NewHashStorage.spec (GF := GF) (hG := hG))
    (hMeta : schema.UnsafeCreateMetaBucket.spec (GF := GF) (hG := hG))
    (hRestore : mvcc.store.restore.spec (GF := GF) (hG := hG))
    (hCLF : mvcc.store.compactLockfree.spec (GF := GF) (hG := hG)) :
    mvcc.NewStore.spec (GF := GF) (hG := hG) :=
  mvcc.NewStore.wp_proofR hNop hNewIdx hFifo hHash hMeta hRestore hCLF

end proof

end EtcdGrove
end Perennial
