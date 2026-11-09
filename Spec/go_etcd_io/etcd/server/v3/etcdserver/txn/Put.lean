/-
## `Put(ctx, lg, lessor, kv, p)` (`put.go`)

**Users.** The apply thread's `applierV3backend.Put` (`apply/backend.go:51`, under the quota and
auth appliers), for a committed `PutRequest`, with `context.TODO()`, the server's lessor and store.
Snippet: `examples/specreq/txn/write.go` (`ReqApplyPutThenRange`, `ReqApplyPutIgnoreValue`,
`ReqApplyPutLeaseCheck`).

**Proof sketch.** `EnsureTrace` (4b), `proto.Size(p)` (2a's `Proto.Size.spec`: `putReqOwn`'s
content by 3h's relation law, depth 2). `checkLease` (its spec, at the pin `leasesPin γ ls`): a
dead lease is `ErrLeaseNotFound`, independent of the store: the caller's update is opened and
committed at once (`putHist` is `h`, ghost step), no transaction. Else `kv.Write(trace)` (3e:
`mvccWriter γ` and the thread token, `mvccTxn tw γ .write h []`, where `h` is learned by peeking
at the caller's update, which also gives `leasesLive h.store ls`; mvcc's writer lock keeps `h` until
`End`). `checkAndGetPrevKV` (its spec at `evs = []`): `ErrKeyNotFound` for an ignore flag on a
missing key (`p.check`'s second case), else the key's record. `put` (its spec: the lease to attach
is `p.Lease`, live by `checkLease`, or the previous record's, live by `leasesLive`). The deferred
`txnWrite.End()` (3e: commits the pending event, firing the caller's update at `h`, the new state
`putHist pr h ls`; on the `ErrKeyNotFound` path, nothing pending: `putHist` is `h`).

**Changes.** The old spec (`specs-ref`'s `Put.lean`: the begin and commit updates `putAU` over the
log, the batch lock's critical section `csA`, the lessor's item map `I`, a premise "the caller gives
its updates only for a live lease") restated: one update, fired once, over W0's history, the answer
W0's (`putAns`); the backend and hook contract folded into 3e's `mvccWriter`; the lessor a pin of its
live leases (the item map is the store's: 3e/3c's coupling); no pin of the store (one write
transaction is atomic by mvcc's writer lock).

**Margin.** None (the reply's header carries only the revision).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **`Put(ctx, lg, lessor, kv, p)`**: at the state `h` the caller's update fires at and the live
leases `ls` (pinned), W0's put: `ErrLeaseNotFound` or `ErrKeyNotFound` (nothing written), or the
key written at revision `h.rev + 1`, its previous key-value if asked. -/
def Put.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (le kv : GoInterface) (γ : MvccName) (p : Loc) (dq : DFrac)
    (pr : PutReq) (ls : Int → Option LeaseRec) (Q : KVHist → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ mvccKV kv γ ∗ lessorAt le γ ∗ threadTok ∗
      mvccWriter γ ∗ leasesPin γ ls ∗ putReqOwn p dq pr ∗
      AU <{ ∃∃ (h : KVHist), ⌜leasesLive h.store ls⌝ ∗ mvccState γ h }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ (putHist pr h ls), COMM Q h }> }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Put)) (Val #ctx)) (Val #lg)) (Val #le)) (Val #kv)) (Val #p))
  {{ (resp tr : Loc) (err : GoInterface), RET (PairV (PairV #resp #tr) #err);
      threadTok ∗ mvccWriter γ ∗ leasesPin γ ls ∗ putReqOwn p dq pr ∗ traceAt tr ∗
      ∃ h : KVHist, Q h ∗
      (match putAns pr h ls with
       | .ok (.put rev prev) => iprop(⌜err = GoInterface.nil⌝ ∗ putOk resp rev prev)
       | .err e => iprop(⌜resp = null⌝ ∗ errIs err e)
       | _ => iprop(False)) }}

end spec
end Txn
end EtcdGrove
end Perennial
