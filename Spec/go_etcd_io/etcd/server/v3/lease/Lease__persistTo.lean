/-
`(*Lease).persistTo(b)` (`lease.go:55`), an internal helper's spec (mirrors the code). **Users**:
`Grant`, `Checkpoint`, under `le.mu`, on the apply thread. **Proof sketch**: `b.BatchTx()`,
`LockInsideApply` (4a's `beHook b Pk f`: `Pk`, the hook run, `Mvcc.hookRun`), 4b's `MustUnsafePutLease` of `{ID, TTL, RemainingTTL}`
(`beLeases b` at `id := ttl`; the remaining TTL not modelled), `Unlock` (deferred). **Changes**
(from `specs-ref`'s `Lease__persistTo.lean`, the critical-section contract `csContractA` over the
tracked buckets): over 4a/4b's provisional names and mvcc's hook contract. **Margin**: the record's `RemainingTTL`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Internal

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Write the object's record into `b`'s lease bucket** (inside an apply). -/
def Lease.persistTo.spec : Prop :=
  ∀ (l : Loc) (b : GoInterface) (B : Int → Option Int) (id t r : w64) (dq1 dq2 dq3 : DFrac)
    (Pk Pre Q Post : IProp GF) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ beHook b Pk f ∗ Pre ∗
      Mvcc.hookRun Pk f Pre Q ∗ (Q ={⊤}=∗ Pk ∗ Post) ∗
      beLeases b B ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ID"] ↦{dq1} id ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ttl"] ↦{dq2} t ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"remainingTTL"] ↦{dq3} r }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!!
      go!"persistTo")) (Val #b))
  {{ RET #(); Post ∗
      beLeases b (fun i => if i = sint.Z id then some (sint.Z t) else B i) ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ID"] ↦{dq1} id ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ttl"] ↦{dq2} t ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"remainingTTL"] ↦{dq3} r }}

end spec
end Lease
end EtcdGrove
end Perennial
