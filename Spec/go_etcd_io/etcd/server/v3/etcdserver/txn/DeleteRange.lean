/-
## `DeleteRange(ctx, lg, kv, dr)` (`delete.go`)

**Users.** The apply thread's `applierV3backend.DeleteRange` (`apply/backend.go:55`, `context.TODO()`).
(The lessor's revocation deletes through mvcc's `TxnDelete`, not this function: `lease/lessor.go:350`.)
Snippet: `examples/specreq/txn/write.go` (`ReqApplyDeleteRange`).

**Proof sketch.** `EnsureTrace` (4b). `kv.Write(trace)` (3e: `mvccWriter γ`, the thread token; the
state `h` learned by peeking at the caller's update). `deleteRange` (its spec at `evs = []`): the
range's present keys `l` at `h.store`, deleted (`delEvents l`), the reply at `viewRev h (delEvents l)`
(`= (h.commit (delEvents l)).rev`); or, with `PrevKv`, the context's error before any delete. The
deferred `End()` (3e: commits the pending events, firing the caller's update with `l`; with nothing
pending after the context's error, the update is closed unfired, given back).

**Changes.** The old spec (`specs-ref`'s `DeleteRange.lean`: `delAU` over the log, `delPend … ok`)
restated over W0's history; the context's error an outcome with the update given back.

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

/-- **`DeleteRange(ctx, lg, kv, dr)`**: at the state `h` the caller's update fires at, the range's
present keys `l` deleted at one revision (none if `l` is empty), the reply counting them (and
listing them with `PrevKv`); or, with `PrevKv` and the context done, its error, nothing written and
the update given back. -/
def DeleteRange.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (kv : GoInterface) (γ : MvccName) (d : Loc) (dq : DFrac)
    (dm : DeleteReq) (Q : KVHist → List KV → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ mvccKV kv γ ∗ threadTok ∗ mvccWriter γ ∗
      deleteReqOwn d dq dm ∗
      AU <{ ∃∃ (h : KVHist), mvccState γ h }> @ ⊤ \ ↑mvccN, ∅
        <{ ∀∀ (l : List KV), ⌜h.store.rangeKVs dm.range l⌝ ∗ mvccState γ (h.commit (delEvents l)),
           COMM Q h l }> }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange)) (Val #ctx)) (Val #lg)) (Val #kv)) (Val #d))
  {{ (resp tr : Loc) (err : GoInterface), RET (PairV (PairV #resp #tr) #err);
      threadTok ∗ mvccWriter γ ∗ deleteReqOwn d dq dm ∗ traceAt tr ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (h : KVHist) (l : List KV), Q h l ∗
          ⌜h.store.rangeKVs dm.range l⌝ ∗
          delOk resp (h.commit (delEvents l)).rev l.length (if dm.prevKv then l else [])) ∨
       (⌜resp = null ∧ dm.prevKv = true⌝ ∗ Context.ctxDone ctx ∗ ctxErr err ∗
          AU <{ ∃∃ (h : KVHist), mvccState γ h }> @ ⊤ \ ↑mvccN, ∅
            <{ ∀∀ (l : List KV), ⌜h.store.rangeKVs dm.range l⌝ ∗ mvccState γ (h.commit (delEvents l)),
               COMM Q h l }>)) }}

end spec
end Txn
end EtcdGrove
end Perennial
