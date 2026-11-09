/-
`(*concurrency.Mutex).tryAcquire(ctx)` (`client/v3/concurrency/mutex.go`), internal.

Users: `Mutex.Lock`, `Mutex.TryLock`.

Proof sketch: `isSession_client` (the client, the lease); `fmt.Sprintf("%s%x", pfx, lease)`
(Perennial's model: the prefix, then some suffix); `CreateRevision.spec`, `Compare.spec`,
`WithLease.spec`, `OpPut.spec`, `OpGet.spec`, `WithFirstCreate.spec`; `isClient_KV`, the KV
contract's `Txn`, `If`, `Then`, `Else`, `Commit` (W0) with the update built from `etcdPerm`
(the step is `keysEff`: the key put with the lease if absent, else nothing); its reply
(`txnReply`): with `etcdLb_init` (`req/go_etcd_io_etcd_client_v3.md`, "from 1d": a present key
has a positive create revision), the comparison held iff the key was absent, so the key has
create revision `c` after the transaction (the header's revision if created, the else-branch's
get otherwise: `Kvs[0]` exists), and the second response is `firstCreate`.

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
  ∀ (m s : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s pfx ∗ mutexSt m st ∗ isSession s γ who id ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗
      etcdPerm γ T ∗ ⌜effIn (keysEff (fun k => pfx <+: k) (sint.Z id)) T⌝ }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"tryAcquire")) (Val #ctx))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ k : GoString, ⌜pfx <+: k⌝ ∗
          mutexSt m { st with key := k }) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (k : GoString) (c : Nat) (σ : State) (mr : TxnRespM),
          mutexSt m { st with key := k, rev := W64 c } ∗ etcdLb γ σ ∗
          txnRespOwn resp (DFrac.own 1) mr ∗
          ⌜pfx <+: k ∧ 0 < c ∧ c ≤ σ.kv.rev ∧ (∃ r, σ.kv.store k = some r ∧ r.createRev = c) ∧
            mr.hdr.revision = W64 σ.kv.rev ∧
            ∃ x owner l, mr.responses = [x, .range owner] ∧ owner.kvs = l.map KeyValueM.ofKV ∧
              firstCreate pfx σ.kv.store l⌝) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
