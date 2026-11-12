/-
## `(*lockServer).Lock(ctx, req)` (`lock.go:33-50`): translated

**Users.** The `Lock` RPC (`etcdctl lock`, `v3lockpb` clients); `ReqLockOverInProc`.
**Proof sketch.** 1d's `NewSession.spec` (the request's lease, the context), `Orphan`, `NewMutex`,
`Mutex.Lock.spec` (the lent permission): the lock fact `lockedSince` at a reached state, or an error.
**Changes** (from `specs-ref`'s `lockServer__Lock.lean`): over 1d's facts.
Changes: verify-round: the prefix is `name ++ "/"` (`NewMutex`'s; A3 completeness F1, A8 provability
F6: `lockedSince name` was false of a key `name ++ "z"` created earlier), in the effect and the fact;
the key is the session's (`sessKey`, 1d's post) under the request's lease when non-zero; the lent
token `P` is given back on success (1d returns it; A3 completeness F7); the messages are 3h's.
**Margin.** As 1d's; on an error `P` is not returned (the error is not classified: a session error
before the mutex, `ErrSessionExpired` and a transport error look alike to the caller).

**The principal** (round 1, completeness F9): the in-process client (`v3client.New(s)`, default
principal `dflt`: none) forwards each call's token, so the call's principal is the context's `who`
(`ClientV3.ctxPrin dflt ctx who`), the effects under it, as 1d's specs state them. `v3client.New`'s
spec (an `isClient … none` from `isServer`) is requested of 1c (`req/…client_v3.md`, "from 2e,
round 1").
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Api

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

/-- **Acquires the lock `name`** (the prefix `name ++ "/"`): its key, the session's, and the lock
fact at a state the cluster reached; the lent token back. -/
def lockServer.Lock.spec : Prop :=
  ∀ (ls c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (σ0 : State) (req : Loc) (name : GoString) (lease : w64) (Ts T : State → State → Prop) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock ∗ isLockServer ls c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗ lockReq req name lease ∗ etcdPerm γ Ts ∗
      ⌜effIn (fun σ σ' => readEff σ σ' ∨ (lease = W64 0 ∧ grantEff 60 σ σ')) Ts⌝ ∗
      etcdLent γ T P ∗ P ∗ ⌜∀ l : Int, effIn (mutexEff (name ++ go!"/") l) T⌝ }}
    (App (App (Val (ls @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.lockServer.ty @!! go!"Lock")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ P ∗ ∃ (k : GoString) (cr : Nat) (id : w64) (σ : State),
          lockResp resp k ∗ etcdLb γ σ ∗
          ⌜Reach σ0 σ ∧ (lease ≠ W64 0 → id = lease) ∧ k = sessKey (name ++ go!"/") (sint.Z id) ∧
            lockedSince (name ++ go!"/") k cr σ⌝) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3lock
end EtcdGrove
end Perennial
