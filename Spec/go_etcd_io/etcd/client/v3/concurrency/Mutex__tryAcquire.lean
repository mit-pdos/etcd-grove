/-
`(*concurrency.Mutex).tryAcquire(ctx)` (`client/v3/concurrency/mutex.go`), internal.

Users: `Mutex.Lock`, `Mutex.TryLock`.

Proof sketch: `isSession_client` (the client, the lease); `fmt.Sprintf("%s%x", pfx, lease)`
(Perennial's model: the prefix, then some suffix); `CreateRevision.spec`, `Compare.spec`,
`WithLease.spec`, `OpPut.spec`, `OpGet.spec`, `WithFirstCreate.spec`; `isClient_KV`, the KV
contract's `Txn`, `If`, `Then`, `Else`, `Commit` (W0) with the update from the lent permission
(the step is `mutexEff`'s put: the key created empty with the lease if absent, else nothing); its
reply (`txnReply`): with `etcdLb_init` (a present key has a create revision `≥ 2`), the comparison
held iff the key was absent, so the key has create revision `c` after the transaction (the
header's revision if created, the else-branch's get otherwise: `Kvs[0]` exists), and the second
response is `firstCreate`. The lent permission (`etcdLent γ T P` with the token `P`): each write's exclusive update
is built from it (giving `P` up, back at the commit), each read's from its `etcdPeek`; the first
firing after the call starts gives `Reach σ0` (`etcdLb_reach`). `P` is returned on every outcome
whose writes have all been answered; an error after which a write may be pending keeps it.

Changes: from `specs-ref`'s `Mutex__tryAcquire.lean`: over W0's reply model and the cluster's
states (`etcdLb`) instead of the old `acquireResp`/`etcdReached`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `m.tryAcquire(ctx)`: the mutex's key (under the prefix) created with the session's lease if absent; the reply, the key's create revision `c` (`myRev`), and the oldest key under the prefix after the transaction. -/
def Mutex.tryAcquire.spec : Prop :=
  ∀ (m s c : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (dflt who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s pfx ∗ mutexSt m st ∗ isSession s c γ id ∗ isClient c γ dflt ∗
      Context.ctxOk ctx ∗ ctxPrin dflt ctx who ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (mutexEff pfx (sint.Z id)) T⌝ }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"tryAcquire")) (Val #ctx))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ k : GoString, ⌜pfx <+: k⌝ ∗
          mutexSt m { st with key := k }) ∨
      (⌜err = GoInterface.nil⌝ ∗ P ∗ ∃ (k : GoString) (cr : Nat) (σ : State) (mr : TxnRespM),
          mutexSt m { st with key := k, rev := W64 cr } ∗ etcdLb γ σ ∗
          txnRespOwn resp (DFrac.own 1) mr ∗
          ⌜Reach σ0 σ ∧ pfx <+: k ∧ 0 < cr ∧ cr ≤ σ.kv.rev ∧
            (∃ r, σ.kv.store k = some r ∧ r.createRev = cr) ∧ mr.hdr.revision = W64 σ.kv.rev ∧
            ∃ x owner l, mr.responses = [x, .range owner] ∧ owner.kvs = l.map KeyValueM.ofKV ∧
              firstCreate pfx σ.kv.store l⌝) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
