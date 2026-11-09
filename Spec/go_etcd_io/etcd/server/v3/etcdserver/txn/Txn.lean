/-
## `Txn(ctx, lg, rt, txnModeWriteWithSharedBuffer, kv, lessor, skipRangeExecution)` (`txn.go`)

**Users.** The request path's read-only transactions (`EtcdServer.Txn`, `v3_server.go:366`, inside
`doSerialize`, `skip` false, the request's context); the apply thread's `applierV3backend.Txn`
(`apply/backend.go:63`, every committed transaction, `context.TODO()`, `skip` when no one waits for
the result: `apply/apply.go:43`). Snippets: `examples/specreq/txn/read.go` (`ReqTxnReadOnly`),
`write.go` (`ReqApplyTxnCAS`, `ReqApplyTxnSkip`).

**Proof sketch.** `IsTxnReadonly` (its spec: `t.readonly`). `kv.Read(mode, trace)` (3e, either
mode): the read transaction at the state `h` (a read-only transaction: the caller's update fires
here, `runHist_readonly` gives `runHist t h ls = h`; a write: a peek, `h = h0` by the pin, and
`attached`). `compareToPath` (its spec: `txnPathOf t h.store`). `checkTxn` (its spec, at the lessor's
writer token for a write): `opsCheck h ls ops`; an error ends the call (`txnRead.End()`; a write's update is
fired at `h`, unchanged: `runHist` is `h` when `run` fails). Else, a write: `txnRead.End()`,
`kv.Write(trace)` (3e: `mvccWriter γ`; the state is still `h0`: the pin, as the sole writer), a
read-only one `mvcc.NewReadOnlyTxnWrite(txnRead)` (3e: kind `.roWrite`). `txn` (its spec: the
responses of `execOps`, the header's revision `runRev`; a write's error is excluded by the context
never done and `txnSafe`, a read-only one's is the context's). `txnWrite.End()` (3e: a write
commits its events, firing the caller's update: the new state `runHist t h0 ls`).

**Changes.** The old spec (`specs-ref`'s `Txn.lean`: two triples by caller, `specSole` with the
read update, a wand to the write updates and the pin `σ.log = log`, `PathsIgnOk`, `leasesKnown`,
`csA`; `specRead`) merged into one: one update, pinned only for a write (`t.readonly ∨ h = h0` in its
precondition), fired once, over W0's history, the run a function (`run`, related to W0's `TxnRun` by
`run_txnRun`); the paths' premises a state-free `txnSafe` (the gRPC layer's checks give it); the
backend share and hook contract in 3e's `mvccWriter`; the lessor 3c's writer token, `attached` kept.

**Margin.** A nested transaction's header revision is `0` (W0 does not model it). The read-only
transaction's response after a context error is partly filled (`roTxnResp`: what the warning reads).
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
/-- **`Txn(ctx, lg, rt, shared, kv, lessor, skip)`**: at the state `h` the caller's update fires at
(a write: the state `h0` it is pinned at, the store's sole writer), `run`: `checkTxn`'s error
(nothing written, no response or trace), or the run's responses (`skip`: ranges unexecuted) with
header revision `runRev`, its events committed at one revision; or, for a read-only transaction
whose context is done, the context's error. -/
def Txn.spec : Prop :=
  ∀ (ctx : GoInterface) (lg rt : Loc) (dq : DFrac) (t : TxnReq) (shared : Bool) (kv le : GoInterface)
    (skip : Bool) (γ : MvccName) (h0 : KVHist) (leL : Loc) (γl : Lease.Names) (c : Lease.Cfg)
    (n : Nat) (ls : Lease.LessorState) (Q : KVHist → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ mvccKV kv γ ∗ threadTok ∗
      txnReqOwn rt dq t ∗ ⌜txnSafe t⌝ ∗
      (if t.readonly then iprop(True)
       else iprop(⌜le = Lease.lessorIface leL⌝ ∗ Lease.isLessor leL γl c ∗ mvccLessor γ γl ∗
         mvccWriter γ ∗ Lease.lessorState γl n ls ∗ (Context.ctxDone ctx -∗ False))) ∗
      AU <{ ∃∃ (h : KVHist), ⌜t.readonly ∨ (h = h0 ∧ attached h.store ls)⌝ ∗ mvccState γ h }>
          @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ (runHist t h ls.table), COMM Q h }> }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Txn)) (Val #ctx)) (Val #lg)) (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp tr : Loc) (err : GoInterface), RET (PairV (PairV #resp #tr) #err);
      threadTok ∗ txnReqOwn rt dq t ∗
      ∃ h : KVHist, Q h ∗ ⌜t.readonly ∨ h = h0⌝ ∗
      (if t.readonly then iprop(True)
       else iprop(mvccWriter γ ∗ ∃ (n' : Nat) (ls' : Lease.LessorState), Lease.lessorState γl n' ls' ∗
         ⌜sameLeases ls ls' ∧ attached (runHist t h ls.table).store ls'⌝)) ∗
      (match run t h ls.table skip with
       | .error e => iprop(⌜resp = null ∧ tr = null⌝ ∗ errIs err e)
       | .ok x => iprop(traceAt tr ∗
           ((⌜err = GoInterface.nil⌝ ∗ txnOk resp (runRev h x.1) x.2.1 x.2.2) ∨
            (⌜t.readonly⌝ ∗ Context.ctxDone ctx ∗ ctxErr err ∗ roTxnResp resp)))) }}

end spec
end Txn
end EtcdGrove
end Perennial
