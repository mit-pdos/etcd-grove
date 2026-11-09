/-
## `DeleteRange(ctx, lg, kv, dr)` (`delete.go`)

**Users.** The apply thread's `applierV3backend.DeleteRange` (`apply/backend.go:55`, `context.TODO()`).
(The lessor's revocation deletes through mvcc's range deleter, not this function.) Snippets:
`examples/specreq/txn/write.go` (`ReqApplyDeleteRange`, `ReqApplyDeletePrevKv`).

**Proof sketch.** `EnsureTrace` (4b's `EnsureTrace.spec`: the context's non-empty trace, whose ownership the caller
lends through `ctxTraceOwn o`, or a fresh one: `traceBack o tr` after). `kv.Write(trace)` (3e's `KV.Write.contract`: the reader token, the
storage's share and `txnWriter`'s hook run under the batch lock; its update a peek at the caller's,
pinned at `σ₀`, `σ₀.pending = []`; `mvccTxn tw γ tr (.write σ₀ [])`). `deleteRange` (its spec at `.write σ₀ []`): the
range's present keys `l` at `σ₀.kv.store` (`rangeAll`, `rangeAll_eq`), deleted (3e's
`Txn.DeleteRange`: the lessor's token by `delsLs`, which is `evsLs` of the deletes), the reply at
the transaction's revision after; or, with `PrevKv`, the context's error before any delete.
The deferred `txnWrite.End()` (3e's `Txn.End.contract`: the
storage's share and `Pk`, from `txnWriter`'s `Q' ={⊤}=∗ Pk ∗ Post`; its two nested updates are the
caller's, at `σ₀`: notify with the events, then the bump, `Q`; with no events (an error after the
begin), both opened and closed unchanged, the caller's update given back).

**Changes.** The old spec (`specs-ref`'s `DeleteRange.lean`: `delAU` over the log) restated over W0's
history. Round 1 (F4): 3e's two-step commit pinned at `σ₀`, `MvccState`, reader tokens, the trace,
`txnWriter`; the lessor's state after exactly (`evsLs`); the lessor's handle dropped (S4: the store's
own, in `isMvcc`).

**Margin.** None.
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

/-- **`DeleteRange(ctx, lg, kv, dr)`**: at the state `σ₀` the caller's update is pinned at, the range's
present keys deleted at one revision (none if there are none), the reply counting them (and listing
them with `PrevKv`); or, with `PrevKv` and the context done, its error, nothing written and the
update given back. -/
def DeleteRange.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option Loc) (lg : Loc) (kv : GoInterface) (γ : Mvcc.MvccName)
    (γl : Lease.Names) (n : Nat) (ls : Lease.LessorState) (d : Loc) (dq : DFrac) (dm : DeleteReq)
    (σ₀ : Mvcc.MvccState) (q : Qp) (B : Mvcc.MvccStorage) (Pk Post Q : IProp GF),
  let au : IProp GF := iprop(AU <{ Mvcc.mvccState γ σ₀ }> @ ⊤ \ ↑Mvcc.mvccN, ∅
    <{ Mvcc.mvccState γ (σ₀.notify (delEvents (rangeAll σ₀.kv.store dm.range))) ∗ ⧖ (Mvcc.evCount (σ₀.kv.commit (delEvents (rangeAll σ₀.kv.store dm.range)))), COMM
       AU <{ Mvcc.mvccState γ (σ₀.notify (delEvents (rangeAll σ₀.kv.store dm.range))) }> @ ⊤ \ ↑Mvcc.mvccN, ∅
         <{ Mvcc.mvccState γ (σ₀.notify (delEvents (rangeAll σ₀.kv.store dm.range))).commitPending, COMM Q }> }>)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ TraceUtil.ctxTraceIs ctx o ∗ ctxTraceOwn o ∗ Zap.isLogger lg ∗
      Mvcc.isMvcc kv γ ∗ Mvcc.mvccLessorIs γ γl ∗ Mvcc.mvccReaders γ 1 ∗ Lease.lessorState γl n ls ∗
      deleteReqOwn d dq dm ∗ Mvcc.mvccBackend γ q B Pk ∗ txnWriter B Pk Post ∗
      ⌜σ₀.pending = []⌝ ∗ au }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange)) (Val #ctx)) (Val #lg)) (Val #kv)) (Val #d))
  {{ (resp tr : Loc) (err : GoInterface), RET (PairV (PairV #resp #tr) #err);
      Mvcc.mvccReaders γ 1 ∗ Mvcc.mvccBackend γ q B Pk ∗ deleteReqOwn d dq dm ∗ traceBack o tr ∗ Post ∗
      ((⌜err = GoInterface.nil⌝ ∗ Q ∗
          (∃ n' : Nat, Lease.lessorState γl n' (evsLs ls σ₀.kv.store (delEvents (rangeAll σ₀.kv.store dm.range)))) ∗
          delOk resp (σ₀.kv.commit (delEvents (rangeAll σ₀.kv.store dm.range))).rev (rangeAll σ₀.kv.store dm.range).length
            (if dm.prevKv then rangeAll σ₀.kv.store dm.range else [])) ∨
       (⌜resp = null ∧ dm.prevKv = true⌝ ∗ Context.ctxDone ctx ∗ ctxErr err ∗
          Lease.lessorState γl n ls ∗ au)) }}

end spec
end Txn
end EtcdGrove
end Perennial
