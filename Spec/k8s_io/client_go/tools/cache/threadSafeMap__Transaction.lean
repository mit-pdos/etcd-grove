/-
`(*threadSafeMap).Transaction(txns...)` (`thread_safe_store.go:269`): the batch path's store write
(`InOrderInformersBatchProcess`): every key's last write applied under the write lock, the resource
version the last object's. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (fourth round).

**Names only** (gap C4, `notes/k8s-clientgo-goose.md`: the slow-trace threshold's
`min(500*time.Millisecond*time.Duration(len(txns)), 5*time.Second)` is rejected by the pinned Goose),
so this spec is a **named hypothesis** (`?` in `etc/link-lean-first-k8scache.txt`), stated as what
the code does (read 2026-10-27, client-go `569675c57fa3`):

```go
if len(txns) == 0 { return }
finalObj := txns[len(txns)-1].Object
rv, rvErr := rvFromObject(finalObj)          // before the lock
rvInt, parseErr := parseRVForMetricsWithTruncation(rv)
lastWrite := map[key]int{}                   // each key's last index
c.lock.Lock(); defer c.lock.Unlock()
trace ...; defer trace.LogIfLong(min(...))   // the gap
for i, txn := range txns {
  if lastWrite[txn.Key] != i { continue }
  switch txn.Type { case Add, Update: c.updateLocked(txn.Key, txn.Object)
                    case Delete: c.deleteLocked(txn.Key) }
}
if rvErr == nil { c.rv = rv; if parseErr == nil { metrics.Set(rvInt) } }
```

For writes of the three known types, applying each key's last write is applying them all in order
(`St.txn`); a write of another type would hide the key's earlier writes, so the spec requires the
known types (`processDeltasInBatch` builds only those). The transaction is one linearization point
(the lock is held throughout); the resource version is the last object's when its accessor has one
(`rvAcc`), else kept, **not monotone** (as `Update`'s). Objects stored meet `OK` (the store's
contract), as `Update` requires; the slice is only read.
-/
module

public import Proof.k8s_io.client_go.tools.cache.BatchDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.Transaction(txns...)`**, logically atomic, for writes `xs` of the known types whose objects
meet `OK` and the accessor's domain `D`: the store becomes `St.txn rvOf σ xs`. -/
abbrev threadSafeMap.Transaction.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (D : GoInterface → IProp GF) (rvOf : GoInterface → Option GoString) (sl : GoSlice)
    (dq : DFrac) (xs : List Tx),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      rvAcc D rvOf ∗ sl ↦*{dq} (xs.map Tx.go) ∗ ⌜∀ x ∈ xs, x.typeOk⌝ ∗
      □ ([∗list] x ∈ xs, D x.o ∗ OK x.o) }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"Transaction")) (Val #sl))
    @@ ∅
  <<{ storeSt γ (St.txn rvOf σ xs) }>>
  {{ RET #(); sl ↦*{dq} (xs.map Tx.go) }}

end spec

end cache
end EtcdGrove
end Perennial
