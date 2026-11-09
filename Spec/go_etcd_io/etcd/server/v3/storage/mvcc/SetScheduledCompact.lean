/-
`SetScheduledCompact(tx, value)` (`store.go:38`). Internal: `updateCompactRev`.
`tx.LockInsideApply()` (the storage's hook run, `Pre` to `Q'`, on the open share `kbOpen B q`; the
lock's observation is the caller's first update, `kbObs`), `UnsafeSetScheduledCompact` (the entry
bound: a 19-byte key and a 17-byte value), the deferred `tx.Unlock()` (`Pk` and the session's
liveness back; the caller's nested update, built at the data the lock read: the write-back's step to
`KeyData.mid D D' = D'` (a session of `Meta` puts only), then the commit's, which changes nothing;
the open share back).

**Changes** from `specs-ref`'s file: over the storage contract (`storageHook`, `hookRun`, `kbObs`) in
place of `batchTxSpecG`, `lockArmS`, `mwLend`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `SetScheduledCompact(tx, value)`: the hook, then the scheduled key written and made visible
(the storage's two-step publication, the second step a no-op for this session). -/
def SetScheduledCompact.spec : Prop :=
  ∀ (B : MvccStorage) (Pk : IProp GF) (q : Qp) (dq : DFrac) (f : GoFunc) (Pre Q' Post R : IProp GF)
    (value : w64),
  let D' (D : KeyData) := D.putMeta .sched (revBytes ⟨value, W64 0⟩ false)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ schemaVars ∗
      keyBackend B Pk ∗ kbOpen B q ∗ storageHook B dq f ∗ Pre ∗ hookRun B Pk f Pre Q' ∗
      (Q' ={⊤}=∗ Pk ∗ Post) ∗
      kbObs B (fun D => iprop(⌜D.metaMade = true⌝ ∗
        AU <{ ∃∃ (D1 : KeyData), kbData B D1 }> @ ⊤, ∅ <{ kbData B (D' D), COMM
          AU <{ ∃∃ (D2 : KeyData), kbData B D2 }> @ ⊤, ∅ <{ kbData B (D' D), COMM R }> }>)) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact))
      (Val #(GoInterface.ok (kbBatchTx B)))) (Val #value))
  {{ RET #(); kbOpen B q ∗ storageHook B dq f ∗ Post ∗ R }}

end spec
end Mvcc
end EtcdGrove
end Perennial
