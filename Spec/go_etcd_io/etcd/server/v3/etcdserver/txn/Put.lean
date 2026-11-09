/-
## `Put(ctx, lg, lessor, kv, p)` (`put.go`)

**Users.** The apply thread's `applierV3backend.Put` (`apply/backend.go:51`, under the quota and
auth appliers), for a committed `PutRequest`, with `context.TODO()`, the server's lessor and store.
Snippets: `examples/specreq/txn/write.go` (`ReqApplyPutThenRange`, `ReqApplyPutIgnoreValue`,
`ReqApplyPutLeaseCheck`).

**Proof sketch.** `EnsureTrace` (4b's `EnsureTrace.spec`: the context's non-empty trace, whose ownership the caller
lends through `ctxTraceOwn o`, or a fresh one: `traceBack o tr` after); `proto.Size(p)` (2a's `Proto.Size.spec`: `putReqOwn`'s content by
3h's relation law, depth 2). `checkLease` (its spec, at the lessor's writer token): a dead lease is
`ErrLeaseNotFound` before any transaction (the update, the writer's resources and the token given
back). Else `kv.Write(trace)` (3e's `KV.Write.contract`: the reader token, the
storage's share and `txnWriter`'s hook run under the batch lock; its update a peek at the caller's,
pinned at `σ₀`, `σ₀.pending = []`; `mvccTxn tw γ tr (.write σ₀ [])`). `checkAndGetPrevKV` (its spec at `.write σ₀ []`): `ErrKeyNotFound` for an
ignore flag on a missing key, else the key's record. `put` (its spec: the lease to attach is
`p.Lease`, live by `checkLease`, or the previous record's, live by `leasesLive`; the lessor's token
moved by 3e's `putLs`, which is `evsLs` of the one event). The deferred `txnWrite.End()` (3e's `Txn.End.contract`: the
storage's share and `Pk`, from `txnWriter`'s `Q' ={⊤}=∗ Pk ∗ Post`; its two nested updates are the
caller's, at `σ₀`: notify with the events, then the bump, `Q`; with no events (an error after the
begin), both opened and closed unchanged, the caller's update given back).

**Changes.** The old spec (`specs-ref`'s `Put.lean`: the begin and commit updates `putAU` over the
log, the batch lock's critical section `csA`, the lessor's item map) restated over W0's history and
answer (`putAns`). Round 1 (`3b-review-1.md`, F4): 3e's two-step commit, the update pinned at `σ₀`
(3e's `Txn.End` needs `σ = σ₀` at the commit, which the store's sole writer gives); `MvccState`;
reader tokens; the caller's trace; the storage's share and `txnWriter` for the provisional writer
slot; the lessor's state after, exactly (`evsLs`, 3e's steps), from `leasesLive` (the code's need)
in place of the attachment invariant (S3).

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

open Classical in
/-- **`Put(ctx, lg, lessor, kv, p)`**: at the state `σ₀` the caller's update is pinned at and the live
leases of the lessor's state `ls`, W0's put (`putAns`): the key written at revision `σ₀.rev + 1`
(the update fired in its two steps, the lessor's attachments moved), its previous key-value if
asked; or `ErrLeaseNotFound`/`ErrKeyNotFound`, nothing written, the update given back. -/
def Put.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option Loc) (lg : Loc) (leL : Loc) (kv : GoInterface)
    (γ : Mvcc.MvccName) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat) (ls : Lease.LessorState)
    (p : Loc) (dq : DFrac) (pr : PutReq) (σ₀ : Mvcc.MvccState) (q : Qp) (B : Mvcc.MvccStorage)
    (Pk Post Q : IProp GF),
  let au : IProp GF := iprop(AU <{ Mvcc.mvccState γ σ₀ }> @ ⊤ \ ↑Mvcc.mvccN, ∅
    <{ Mvcc.mvccState γ (σ₀.notify (putEvents pr σ₀.kv)) ∗ ⧖ (Mvcc.evCount (σ₀.kv.commit (putEvents pr σ₀.kv))), COMM
       AU <{ Mvcc.mvccState γ (σ₀.notify (putEvents pr σ₀.kv)) }> @ ⊤ \ ↑Mvcc.mvccN, ∅
         <{ Mvcc.mvccState γ (σ₀.notify (putEvents pr σ₀.kv)).commitPending, COMM Q }> }>)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ TraceUtil.ctxTraceIs ctx o ∗ ctxTraceOwn o ∗ Zap.isLogger lg ∗
      Mvcc.isMvcc kv γ ∗ Mvcc.mvccLessorIs γ γl ∗ Lease.isLessor leL γl c ∗ Mvcc.mvccReaders γ 1 ∗
      Lease.lessorState γl n ls ∗ putReqOwn p dq pr ∗ Mvcc.mvccBackend γ q B Pk ∗ txnWriter B Pk Post ∗
      ⌜σ₀.pending = [] ∧ leasesLive σ₀.kv.store ls⌝ ∗ au }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Put)) (Val #ctx)) (Val #lg)) (Val #(Lease.lessorIface leL))) (Val #kv)) (Val #p))
  {{ (resp tr : Loc) (err : GoInterface), RET (PairV (PairV #resp #tr) #err);
      Mvcc.mvccReaders γ 1 ∗ Mvcc.mvccBackend γ q B Pk ∗ putReqOwn p dq pr ∗ traceBack o tr ∗
      (match putAns pr σ₀.kv ls.table with
       | .ok (.put rev prev) => iprop(⌜err = GoInterface.nil⌝ ∗ putOk resp rev prev ∗ Q ∗ Post ∗
           ∃ n' : Nat, Lease.lessorState γl n' (evsLs ls σ₀.kv.store (putEvents pr σ₀.kv)))
       | .err e => iprop(⌜resp = null⌝ ∗ errIs err e ∗ au ∗ Lease.lessorState γl n ls ∗
           (if e = .leaseNotFound then txnWriter B Pk Post else Post))
       | _ => iprop(False)) }}

end spec
end Txn
end EtcdGrove
end Perennial
