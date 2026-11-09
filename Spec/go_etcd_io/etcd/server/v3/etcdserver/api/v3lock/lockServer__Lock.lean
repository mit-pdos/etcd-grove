/-
## `(*lockServer).Lock(ctx, req)` (`lock.go:33-50`): translated

**Users.** The `Lock` RPC (`etcdctl lock`, `v3lockpb` clients).
**Proof sketch.** 1d's `NewSession.spec` (the request's lease, the context), `Orphan`, `NewMutex`,
`Mutex.Lock.spec`: the lock fact `lockedSince` at a reached state, or an error.
**Changes** (from `specs-ref`'s `lockServer__Lock.lean`): over 1d's facts. **Margin.** As 1d's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3lock

open Iris Iris.BI EtcdModel ClientV3 Concurrency

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Assumptions]

/-- **Acquires the lock `name`**: its key and the lock fact. -/
def lockServer.Lock.spec : Prop :=
  ∀ (ls c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (req : Loc)
    (name : GoString) (lease : w64) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock ∗ isLockServer ls c ∗ ClientV3.isClient c γ who ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin ctx who ∗ lockReq req name lease ∗
      etcdPerm γ T ∗ ⌜effIn (fun σ σ' => readEff σ σ' ∨ (lease = W64 0 ∧ grantEff 60 σ σ')) T ∧
        ∀ l : Int, effIn (keysEff (fun k => name <+: k) l) T⌝ ∗ threadTok }}
    (App (App (Val (ls @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.lockServer.ty @!! go!"Lock")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (k : GoString) (cr : Nat) (σ : State), lockResp resp k ∗
          etcdLb γ σ ∗ ⌜lockedSince name k cr σ⌝) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3lock
end EtcdGrove
end Perennial
