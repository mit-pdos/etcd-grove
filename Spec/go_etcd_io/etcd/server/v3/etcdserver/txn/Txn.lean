/-
## `Txn(ctx, lg, rt, txnModeWriteWithSharedBuffer, kv, lessor, skipRangeExecution)` (`txn.go`)

**Users.** The request path's read-only transactions (`EtcdServer.Txn`, `v3_server.go:366`, inside
`doSerialize`, `skip` false, the request's context); the apply thread's `applierV3backend.Txn`
(`apply/backend.go:63`, every committed transaction, `context.TODO()`, `skip` when no one waits for
the result: `apply/apply.go:43`). Snippets: `examples/specreq/txn/read.go` (`ReqTxnReadOnly`),
`write.go` (`ReqApplyTxnCAS`, `ReqApplyTxnSkip`, `ReqApplyTxnCheckFails`).

**Proof sketch.** `EnsureTrace` (4b's `EnsureTrace.spec`: the context's non-empty trace, whose ownership the caller
lends through `ctxTraceOwn o`, or a fresh one: `traceBack o tr` after). `IsTxnReadonly` (`t.readonly`). `kv.Read(mode, trace)` (3e's
`KV.Read.contract`, either mode): a read-only transaction fires the caller's update here, at `σ`
(`runEvs_readonly`); a write peeks at its pinned update (`σ = σ₀`). `compareToPath` (its spec:
`txnPathOf t σ.kv.store`). `checkTxn` (its spec, at the read transaction; for a write, at the
lessor's writer token): `opsCheck`; an error ends the call (`txnRead.End()`: the reader token back;
a write's update, writer resources and token given back). Else, a write: `txnRead.End()`,
`kv.Write(trace)` (3e's `KV.Write.contract`: the reader token, the
storage's share and `txnWriter`'s hook run under the batch lock; its update a peek at the caller's,
pinned at `σ₀`, `σ₀.pending = []`; `mvccTxn tw γ tr (.write σ₀ [])`) (still `σ₀`: the pin); a read-only one `mvcc.NewReadOnlyTxnWrite(txnRead)` (3e: still
`.read σ`). `txn` (its spec: the responses of `execOps`, the header's revision `runRev`; a write's
error is excluded by the context never done and `txnSafe`, a read-only one's is the context's).
`txnWrite.End()`: for a write, 3e's two steps of the caller's update with the run's events, then
`Q σ₀`.

**Changes.** The old spec (`specs-ref`'s `Txn.lean`: two triples by caller, `specSole` with a wand
from the read update to the write updates, `PathsIgnOk`, `leasesKnown`, `csA`; `specRead`) merged
into one, a case split on the input: a read-only transaction's update is a read's; a writing one's
is pinned at `σ₀` and nested as 3e's commit. The run a function (`run`, related to W0's `TxnRun` by
`run_txnRun`); the paths' premises a state-free `txnSafe`. Round 1 (F4): 3e's API (`MvccState`,
reader tokens, the trace, the storage's share and `txnWriter`, the lessor's state after by
`evsLs`).

**Margin.** A nested transaction's header revision is `0` (W0 does not model it). `txnSafe` is
stricter than the code needs (its docstring). A read-only transaction's response after a context
error is partly filled (`roTxnResp`: what the warning reads).
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
/-- **`Txn(ctx, lg, rt, shared, kv, lessor, skip)`**: `run` at the state the caller's update fires at
(a read-only transaction: any, `σ`; a writing one: `σ₀`, its update pinned there and nested as
mvcc's commit): `checkTxn`'s error (nothing written, no response or trace, a writing transaction's
update given back), or the run's responses (`skip`: ranges unexecuted) with header revision
`runRev`, a writing one's events committed at one revision; or, for a read-only transaction whose
context is done, the context's error. -/
def Txn.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option Loc) (lg rt : Loc) (dq : DFrac) (t : TxnReq) (shared : Bool)
    (kv le : GoInterface) (skip : Bool) (γ : Mvcc.MvccName) (σ₀ : Mvcc.MvccState) (leL : Loc)
    (γl : Lease.Names) (c : Lease.Cfg) (n : Nat) (ls : Lease.LessorState) (q : Qp)
    (B : Mvcc.MvccStorage) (Pk Post : IProp GF) (Q : Mvcc.MvccState → IProp GF),
  let au : IProp GF := iprop(AU <{ Mvcc.mvccState γ σ₀ }> @ ⊤ \ ↑Mvcc.mvccN, ∅
    <{ Mvcc.mvccState γ (σ₀.notify (runEvs t σ₀.kv ls.table)) ∗ ⧖ (Mvcc.evCount (σ₀.kv.commit (runEvs t σ₀.kv ls.table))), COMM
       AU <{ Mvcc.mvccState γ (σ₀.notify (runEvs t σ₀.kv ls.table)) }> @ ⊤ \ ↑Mvcc.mvccN, ∅
         <{ Mvcc.mvccState γ (σ₀.notify (runEvs t σ₀.kv ls.table)).commitPending, COMM Q σ₀ }> }>)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ TraceUtil.ctxTraceIs ctx o ∗ ctxTraceOwn o ∗ Zap.isLogger lg ∗
      Mvcc.isMvcc kv γ ∗ Mvcc.mvccReaders γ 1 ∗ txnReqOwn rt dq t ∗ ⌜txnSafe t⌝ ∗
      (if t.readonly then iprop(AU <{ ∃∃ (σ : Mvcc.MvccState), Mvcc.mvccState γ σ }> @ ⊤ \ ↑Mvcc.mvccN, ∅
        <{ Mvcc.mvccState γ σ, COMM Q σ }>)
       else iprop(⌜le = Lease.lessorIface leL ∧ σ₀.pending = [] ∧ leasesLive σ₀.kv.store ls⌝ ∗
         Lease.isLessor leL γl c ∗ Mvcc.mvccLessorIs γ γl ∗ Lease.lessorState γl n ls ∗
         Mvcc.mvccBackend γ q B Pk ∗ txnWriter B Pk Post ∗ (Context.ctxDone ctx -∗ False) ∗ au)) }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Txn)) (Val #ctx)) (Val #lg)) (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp tr : Loc) (err : GoInterface), RET (PairV (PairV #resp #tr) #err);
      Mvcc.mvccReaders γ 1 ∗ txnReqOwn rt dq t ∗
      (if t.readonly then
         iprop(∃ σ : Mvcc.MvccState, Q σ ∗
           match run t σ.kv ls.table skip with
           | .error e => iprop(⌜resp = null ∧ tr = null⌝ ∗ errIs err e ∗ ctxTraceOwn o)
           | .ok x => iprop(traceBack o tr ∗
               ((⌜err = GoInterface.nil⌝ ∗ txnOk resp (runRev σ.kv x.1) x.2.1 x.2.2) ∨
                (Context.ctxDone ctx ∗ ctxErr err ∗ roTxnResp resp))))
       else iprop(Mvcc.mvccBackend γ q B Pk ∗
           match run t σ₀.kv ls.table skip with
           | .error e => iprop(⌜resp = null ∧ tr = null⌝ ∗ errIs err e ∗ ctxTraceOwn o ∗ au ∗
               Lease.lessorState γl n ls ∗ txnWriter B Pk Post)
           | .ok x => iprop(⌜err = GoInterface.nil⌝ ∗ traceBack o tr ∗
               txnOk resp (runRev σ₀.kv x.1) x.2.1 x.2.2 ∗ Q σ₀ ∗ Post ∗
               ∃ n' : Nat, Lease.lessorState γl n' (evsLs ls σ₀.kv.store x.1)))) }}

end spec
end Txn
end EtcdGrove
end Perennial
