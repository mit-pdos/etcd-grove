/-
# The `txn` package's specs over mvcc's API (round 16, `d810bc697a`): a draft

Scratch file (outside the repository, never committed); typechecks against the worktree
`mvcc-api`'s build (`lake env lean FILE` from the worktree). Names are under `txn.api` to sit
beside today's specs; adopted, each `txn.api.<F>.spec` replaces today's `txn.<F>.spec` in its spec
file and the prefix goes. The design: `~/mvcc-api-candidates/clients-txn.md`.

Every mvcc fact used is the API's (`Spec/.../storage/mvcc/Api.lean`, round 16): the contracts
`KV.Read`, `KV.Write`, `Txn.Rev`, `Txn.FirstRev`, `Txn.Range` (with its `stateOk` of every readable
state: the sort's premise), `Txn.Put`, `Txn.DeleteRange`, `Txn.Changes`, `Txn.End` (with its notify
receipt, passed to the caller), `NewReadOnlyTxnWrite.spec`, and the laws `shapes`, `persistent`,
`mvccState_reachable`. No internal mvcc predicate appears below; the mvcc definitions it names
(pure, or `isLessor`/`txnCtx`/...) are listed in clients-txn.md §6 for re-export.
-/
import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Txn
import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.txn
import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeTxn
import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Put
import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange
import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range
import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Count

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccReachable MvccName BkRef mvccN mvccLeases)

/-! ## The vocabulary (pure) -/

/-- The state a transaction's reads see: a read transaction's committed state, a write
transaction's pending one. -/
def txn.api.mstate : MTxn → List EtcdKv
  | .read σ => mvcc.stateAfter σ.log
  | .write σ pend => txn.pendState σ.log pend

/-- A read transaction (the read-only wrapper's kind). -/
def txn.api.MTxn.isRead : MTxn → Bool
  | .read _ => true
  | .write _ _ => false

/-- The transaction after the changes `chs` (a read transaction's is unchanged: `executeTxn`'s
read-only runs make none). -/
def txn.api.MTxn.append : MTxn → List mvcc.Change → MTxn
  | .read σ, _ => .read σ
  | .write σ pend, chs => .write σ (pend ++ chs)

/-- What txn knows of every state it reads at an update (`mvccState_reachable`), carried to the
internal specs: reachable, room for its revisions. -/
def txn.api.Reach (σ : MvccState) : Prop := MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63

/-- **A put's pending changes** at the state `σ₀` its write transaction began at: none if it needs
the previous key-value and the key has none (`ErrKeyNotFound`), else its one change. -/
def txn.api.putPend (o : OpFull) (σ₀ : MvccState) : List mvcc.Change :=
  if txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter σ₀.log) = none then []
  else [txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log))]

/-- **A delete's pending changes**: the range's keys at `σ₀`'s state (`delChanges`), or none when
its `PrevKv` range read failed with the context's error (`ok = false`). -/
def txn.api.delPend (o : OpFull) (σ₀ : MvccState) (ok : Bool) : List mvcc.Change :=
  if ok then txn.delChanges (mvcc.stateAfter σ₀.log) o else []

/-- `Txn`'s premise at the log it runs at: today's `TxnPre` without its two size conjuncts (room
for a revision is `mvccState_reachable`'s, the sort's premise `Txn.Range`'s `stateOk`). -/
def txn.api.TxnPreA (log : mvcc.Log) (t : TxnModel) : Prop :=
  txn.OpsOk true (mvcc.stateAfter log) (W64 (log.length : Int)) (mvcc.stateAfter log)
    (t.branch (txn.txnOk (mvcc.stateAfter log) t))

/-- The changes `Txn` makes at the log `log`. -/
abbrev txn.api.txnChs (log : mvcc.Log) (t : TxnModel) : List mvcc.Change :=
  (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-! ## The vocabulary (the caller's updates, as the API's contracts take them) -/

/-- **The caller's update at a read** (`KV.Read`'s, `KV.Range`'s): the state unchanged, `Q σ`. -/
abbrev txn.api.readAU (γ : MvccName) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvcc.api.mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ mvcc.api.mvccState γ σ, COMM Q σ }>)

/-- **The caller's update at a write transaction's begin** (`KV.Write`'s): nothing pending, the
state unchanged, `R σ` (the caller gives `R σ`: for the sole writer, its pin and the next
updates). -/
abbrev txn.api.beginAU (γ : MvccName) (R : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvcc.api.mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ.pending = none⌝ ∗ mvcc.api.mvccState γ σ, COMM R σ }>)

/-- **The caller's two updates at a write transaction's `End`** (`Txn.End`'s, at the state `σ₀` it
began at, with the changes `pend`): the notification (mvcc gives with it the receipt of the history
it makes, round 16, which the caller keeps: the server's `LogSmall`), then the commit, then `Q`. -/
abbrev txn.api.commitAU (γ : MvccName) (σ₀ : MvccState) (pend : List mvcc.Change) (Q : IProp GF) :
    IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvcc.api.mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ = σ₀⌝ ∗ mvcc.api.mvccState γ (σ.notify pend) ∗ ⧖ (mvcc.logCh (σ.log ++ [pend])), COMM
      AU <{ ∃∃ (σ' : MvccState), mvcc.api.mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvcc.api.mvccState γ σ'.commitPending, COMM Q }> }>)

/-- **The critical section under the store's batch lock** (today's `csContract`, in the API's
terms: `Write` runs the hook from `Pre` to `Q` under the lock, `hookRun`, which also covers a `nil`
hook; txn turns `Q` into the lock's invariant and `Post` before `End`). -/
def txn.api.csA (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(Pre ∗ mvcc.api.hookRun P f Pre Q ∗ (Q ={⊤}=∗ P ∗ Post))

/-- **The writer's backend**: a share of the store's backend `B` (batch-lock invariant `P`) and its
hook `f` (persistent). -/
def txn.api.kvBackend (γ : MvccName) (q : Qp) (B : BkRef) (P : IProp GF) (f : GoFunc) :
    IProp GF :=
  iprop(mvcc.api.mvccBackend γ q B P ∗ mvcc.api.hookIs B f)

/-- **A put's updates**: the begin (the caller gives the lessor's item map `I` at the state, and,
for `IgnoreLease`, that the key's lease is live), then the commit of `putPend o σ₀`, then `R σ₀`. -/
def txn.api.putAU (γ : MvccName) (o : OpFull) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (R : MvccState → IProp GF) : IProp GF :=
  txn.api.beginAU γ (fun σ₀ =>
    iprop(⌜mvcc.pendItems σ₀.log [] = I⌝ ∗
      (if o.ignoreLease then txn.leaseOk L (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log)))
       else iprop(True)) ∗
      txn.api.commitAU γ σ₀ (txn.api.putPend o σ₀) (R σ₀)))

/-- **A delete's updates**: the begin (the item map `I` at the state), then the commit of the
deletes (or, after a context error, of nothing), then `R σ₀ ok`. -/
def txn.api.delAU (γ : MvccName) (o : OpFull)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (R : MvccState → Bool → IProp GF) :
    IProp GF :=
  txn.api.beginAU γ (fun σ₀ =>
    iprop(⌜mvcc.pendItems σ₀.log [] = I⌝ ∗
      ∀ ok : Bool, txn.api.commitAU γ σ₀ (txn.api.delPend o σ₀ ok) (R σ₀ ok)))

/-- **`Txn`'s write updates at the sole writer of `log`** (a request that writes): the begin, where
the caller gives the pin (the state's log is `log`: no commit since the read), then the commit of
the run's changes at `log`, then `Qw σ`. The caller builds them from its read update's `Qr`, only
once the checks passed (`Txn.specSole`'s wand), so that a failed check leaves its resources in `Qr`. -/
def txn.api.txnBeginAU (γ : MvccName) (log : mvcc.Log) (t : TxnModel) (Qw : MvccState → IProp GF) :
    IProp GF :=
  txn.api.beginAU γ (fun σ =>
    iprop(⌜σ.log = log⌝ ∗ txn.api.commitAU γ σ (txn.api.txnChs log t) (Qw σ)))

end vocab

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

/-! ## The entry points (logically atomic: the caller's updates passed through) -/

/-- **`Range(ctx, lg, kv, r, withTotalCount)`**: a read transaction at the state `σ` of the
caller's update (`Q σ`), and `rangeResult` there (the sort's premise from `Txn.Range`'s
`stateOk`). Callers: the apply thread (its `Q` pins `σ.log`
to its log), the server's read path (its `Q` gives the floor and its model of `σ.log`). -/
abbrev txn.api.Range.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (kv : GoInterface) (γ : MvccName) (r : Loc) (o : OpFull) (withTotal : Bool) (ot : Option Loc)
    (te : Bool) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.rangeRequestIs r o ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      (if nd then mvcc.neverDone cd else iprop(True)) ∗ ⌜lg ≠ null⌝ ∗ ⌜txn.validSortTarget o⌝ ∗
      txn.api.readAU γ Q }}
    (App (App (App (App (App (Val (@! txn.Range)) (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #kv))
      (Val #r)) (Val #withTotal))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ ⌜trace ≠ null⌝ ∗ (∃ te' : Bool, traceutil.ownTrace trace te') ∗
      ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
      ∃ σ : MvccState, Q σ ∗ ⌜txn.api.Reach σ⌝ ∗
        txn.rangeResult resp err σ.log (W64 (σ.rev : Int)) σ.crev o withTotal ∗
        txn.rangeHdr resp err ∗
        ⌜nd = true → err = GoInterface.nil ∨ sint.Z (W64 (σ.rev : Int)) < sint.Z o.base.rev ∨
          sint.Z (mvcc.rangeRev (W64 (σ.rev : Int)) o.base.rev) < σ.crev⌝ }}

/-- **`Count(ctx, lg, kv, key, rangeEnd, revision)`**: as today, at the state of the caller's
update. -/
abbrev txn.api.Count.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (kv : GoInterface)
    (γ : MvccName) (key rangeEnd : GoSlice) (k e : GoString) (revision : w64) (ot : Option Loc)
    (te : Bool) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ key ↦*□ k ∗ rangeEnd ↦*□ e ∗
      mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      ⌜lg ≠ null⌝ ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗ txn.api.readAU γ Q }}
    (App (App (App (App (App (App (Val (@! txn.Count)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #kv)) (Val #key)) (Val #rangeEnd)) (Val #revision))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜txn.api.Reach σ⌝ ∗
        ((⌜err = GoInterface.nil ∧ sint.Z revision ≤ (σ.rev : Int) ∧
            n = W64 ((rangeIn (mvcc.stateAt σ.log (sint.nat (mvcc.rangeRev (W64 (σ.rev : Int)) revision)))
              (txn.countOp k (txn.rangeEndOf rangeEnd e) revision)).length : Int)⌝) ∨
         (⌜(σ.rev : Int) < sint.Z revision ∧ n = W64 0⌝ ∗ ∃ ef : GoInterfaceOk,
            globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∨
         (⌜sint.Z revision ≤ (σ.rev : Int) ∧
            sint.Z (mvcc.rangeRev (W64 (σ.rev : Int)) revision) < σ.crev ∧ n = W64 0⌝ ∗
            ∃ ec : GoInterfaceOk,
            globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝)) }}

/-- **`Put(ctx, lg, lessor, kv, p)`**: the lease check first (the lessor's owner `L I`); not found,
`ErrLeaseNotFound`, no transaction (`Pre` back; the caller gives its updates only for a live
lease, which it knows from `L`: so none is left unused); else one write
transaction, begun at the state `σ₀` of the caller's update (`putAU`), its `ErrKeyNotFound` (no
change) or its put committed (`putPend o σ₀`) by the caller's two updates, the hook run once under
the batch lock (`Post`). The caller's pin, if any, is in its `R`. -/
abbrev txn.api.Put.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (le kv : GoInterface)
    (γ : MvccName) (p : Loc) (o : OpFull) (q : Qp) (B : BkRef) (P Pre Q Post : IProp GF)
    (f : GoFunc) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (ot : Option Loc) (te : Bool) (R : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.isTxnLessor le (mvccLeases γ) ∗
      lease.lessorUser (mvccLeases γ) L I ∗ txn.putRequestIs p o ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      txn.api.kvBackend γ q B P f ∗ txn.api.csA P f Pre Q Post ∗
      (if decide (o.leaseID = W64 0 ∨ o.leaseID ∈ L) then txn.api.putAU γ o L I R
       else iprop(True)) }}
    (App (App (App (App (App (Val (@! txn.Put)) (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le))
      (Val #kv)) (Val #p))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ txn.api.kvBackend γ q B P f ∗ ⌜trace ≠ null⌝ ∗
      (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
      ((⌜o.leaseID ≠ W64 0 ∧ o.leaseID ∉ L ∧ resp = null⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ Pre ∗
          lease.lessorUser (mvccLeases γ) L I) ∨
       ∃ σ₀ : MvccState, ⌜txn.api.Reach σ₀ ∧ σ₀.pending = none⌝ ∗ Post ∗ R σ₀ ∗
        ((⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter σ₀.log) = none ∧
              resp = null⌝ ∗
            txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∗
            lease.lessorUser (mvccLeases γ) L I) ∨
         (⌜err = GoInterface.nil ∧
              (txn.needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter σ₀.log)).isSome)⌝ ∗
            txn.putResponseIs resp (W64 (σ₀.log.length : Int))
              (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter σ₀.log) else none) ∗
            txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) ∗
            txn.leaseOk L (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log))) ∗
            lease.lessorUser (mvccLeases γ) L (mvcc.pendItems σ₀.log (txn.api.putPend o σ₀))))) }}

/-- **`DeleteRange(ctx, lg, kv, dr)`**: one write transaction, begun at the state `σ₀` of the
caller's update (`delAU`), the range's keys at `σ₀` deleted, committed by the caller's two
updates (`delPend o σ₀ true`), the response; or, with `PrevKv`, the range read's context error
(not at a context never canceled), nothing deleted (`delPend o σ₀ false = []`). `Post` either way. -/
abbrev txn.api.DeleteRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (kv : GoInterface) (γ : MvccName) (dr : Loc) (o : OpFull) (q : Qp) (B : BkRef)
    (P Pre Q Post : IProp GF) (f : GoFunc) (ot : Option Loc) (te : Bool) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (R : MvccState → Bool → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.deleteRangeRequestIs dr o ∗
      lease.leaseOwn (mvccLeases γ) L I ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
      traceutil.ownTraceOpt ot te ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      txn.api.kvBackend γ q B P f ∗ txn.api.csA P f Pre Q Post ∗ txn.api.delAU γ o I R }}
    (App (App (App (App (Val (@! txn.DeleteRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #kv)) (Val #dr))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ txn.api.kvBackend γ q B P f ∗ ⌜trace ≠ null⌝ ∗ Post ∗
      (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
      ∃ σ₀ : MvccState, ⌜txn.api.Reach σ₀ ∧ σ₀.pending = none⌝ ∗
        ((⌜err = GoInterface.nil⌝ ∗ R σ₀ true ∗
            txn.deleteRangeResponseIs resp
              (W64 ((mvcc.writeRev σ₀.log (txn.delChanges (mvcc.stateAfter σ₀.log) o) : Nat) : Int))
              (rangeIn (mvcc.stateAfter σ₀.log) o).length
              (if o.base.prevKV then rangeIn (mvcc.stateAfter σ₀.log) o else []) ∗
            txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
            lease.leaseOwn (mvccLeases γ) L
              (mvcc.pendItems σ₀.log (txn.delChanges (mvcc.stateAfter σ₀.log) o))) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗ R σ₀ false ∗
            lease.leaseOwn (mvccLeases γ) L I)) }}

/-- **`Txn(...)` at the sole writer of `log`** (the apply thread), at a context never canceled:
the read transaction at the caller's read update, whose commit the caller gives with the pin
(`σ.log = log`) and `Qr σ`; for a request that writes, once the checks passed, txn turns `Qr σ`
into the write updates by the caller's wand (`txnBeginAU`: the begin, with the pin again, then the
commit of the run's changes). Either one of `checkTxn`'s errors (no response, no trace, nothing
written, `Pre`, `Qr σ` back), or the
server's transaction at `log` (`srvRunTxn`), its response with header revision `writeRev log chs`,
the leases still known; a write request's under the batch lock (`Post`) and committed by the
caller's updates (`Qw σ`), a read-only one on the read transaction (`Pre`). No size premise: every
sort's from `Txn.Range`'s `stateOk`, at the read transaction or at the write transaction's pending
state. -/
abbrev txn.api.Txn.specSole : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc) (shared : Bool)
    (kv le : GoInterface) (skip : Bool) (γ : MvccName) (log : mvcc.Log) (t : TxnModel) (q : Qp)
    (B : BkRef) (P Pre Q Post : IProp GF) (f : GoFunc) (L : List w64) (ot : Option Loc) (te : Bool)
    (Qr Qw : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.api.kvBackend γ q B P f ∗
      txn.isTxnLessor le (mvccLeases γ) ∗ txn.txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ mvcc.neverDone cd ∗
      txn.leasesKnown L (mvcc.stateAfter log) ∗
      lease.lessorUser (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
      ⌜txn.api.TxnPreA log t⌝ ∗
      txn.api.csA P f Pre Q Post ∗
      txn.api.readAU γ (fun σ => iprop(⌜σ.log = log⌝ ∗ Qr σ)) ∗
      (if txn.txnReadonly t then iprop(True)
       else iprop(∀ σ : MvccState, Qr σ -∗ txn.api.txnBeginAU γ log t Qw)) }}
    (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ txn.api.kvBackend γ q B P f ∗
      ∃ σr : MvccState, ⌜σr.log = log ∧ txn.api.Reach σr⌝ ∗
      ((⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil ∧
            (txn.txnLeased t → ¬ (txn.PathsIgnOk (mvcc.stateAfter log)
              (t.branch (txn.txnOk (mvcc.stateAfter log) t)) ∧ txn.PathsLeaseOk (mvcc.stateAfter log)
              L (t.branch (txn.txnOk (mvcc.stateAfter log) t))))⌝ ∗ txn.checkErrIs err ∗
          Pre ∗ Qr σr ∗
          lease.lessorUser (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
          (∃ (t' : Loc) (te' : Bool), traceutil.ownTrace t' te' ∗
            ⌜∀ t0, ot = some t0 → te = false → t' = t0⌝)) ∨
       (⌜err = GoInterface.nil ∧ trace ≠ null ∧
          (txn.txnReadonly t = true → txn.api.txnChs log t = []) ∧
          txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t)) ∧
          txn.PathsLeaseOk (mvcc.stateAfter log) L (t.branch (txn.txnOk (mvcc.stateAfter log) t))⌝ ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
        txn.txnResponseIs skip resp
          (W64 (mvcc.writeRev log (txn.api.txnChs log t) : Int)) t
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
        txn.leasesKnown L (mvcc.stateAfter (mvcc.commitLog log (txn.api.txnChs log t))) ∗
        lease.lessorUser (mvccLeases γ) L
          (mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog log (txn.api.txnChs log t)))) ∗
        (if txn.txnReadonly t then iprop(Pre ∗ Qr σr)
         else iprop(Post ∗ ∃ σw : MvccState, ⌜σw.log = log⌝ ∗ Qw σw)))) }}

/-- **`Txn(...)` at a reader** (the server's read-only transactions): a read-only request, the
read transaction at the state `σ` of the caller's update (`Q σ`), any context. One of `checkTxn`'s
errors; or the server's run at `σ.log`, header revision `σ.rev`; or the context done during a
range: `fmt.Errorf`'s error, the response partly filled. -/
abbrev txn.api.Txn.specRead : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc) (shared : Bool)
    (kv le : GoInterface) (skip : Bool) (γ : MvccName) (t : TxnModel) (ot : Option Loc) (te : Bool)
    (Q : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.isTxnLessor le (mvccLeases γ) ∗
      txn.txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
      traceutil.ownTraceOpt ot te ∗ ⌜lg ≠ null ∧ txn.txnReadonly t = true ∧ txn.txnGetsOk t⌝ ∗
      txn.api.readAU γ Q }}
    (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜txn.api.Reach σ⌝ ∗
        ((⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗ txn.checkErrIs err ∗
          (∃ (t' : Loc) (te' : Bool), traceutil.ownTrace t' te' ∗
            ⌜∀ t0, ot = some t0 → te = false → t' = t0⌝)) ∨
         (⌜err = GoInterface.nil ∧ trace ≠ null⌝ ∗
           (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
           txn.txnResponseIs skip resp (W64 (σ.rev : Int)) t
             (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).1
             (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 ∗
           txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)) ∨
         (⌜trace ≠ null⌝ ∗ (∃ te' : Bool, traceutil.ownTrace trace te') ∗
           ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
           mvcc.errorfIs err ∗ txn.roTxnRespRd resp ∗
           txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp))) }}

abbrev txn.api.Txn.spec : Prop := txn.api.Txn.specSole (GF := GF) ∧ txn.api.Txn.specRead (GF := GF)

/-! ## The internal functions, at a transaction `mvccTxn t γ trace k` (the trace lent per call) -/

/-- `checkRange(rv, req)` on a read transaction at `σ`. (Superseded 2026-11-05, decided by the
coordinator: `⌜Reach σ⌝` added, `notes/mvcc-migration/txn.md` gap B.) -/
abbrev txn.api.checkRange.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (σ : MvccState) (req : Loc) (o : OpFull),
  {{ pkgInit ∗ mvcc.api.mvccTxn t γ trace (.read σ) ∗ ⌜txn.api.Reach σ⌝ ∗ txn.rangeRequestIs req o }}
    (App (App (Val (@! txn.checkRange)) (Val #t)) (Val #req))
  {{ (err : GoInterface), RET #err; mvcc.api.mvccTxn t γ trace (.read σ) ∗
      txn.checkRangeErr (W64 (σ.rev : Int)) σ.crev o err }}

/-- `applyCompare(rv, c)` on a read transaction at `σ`: `cmpHolds` at its state. -/
abbrev txn.api.applyCompare.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (c : Loc)
    (cm : CmpModel),
  {{ pkgInit ∗ mvcc.api.mvccTxn t γ trace (.read σ) ∗ traceutil.ownTrace trace te ∗
      ⌜txn.api.Reach σ⌝ ∗ txn.compareIs c cm }}
    (App (App (Val (@! txn.applyCompare)) (Val #t)) (Val #c))
  {{ RET #(cmpHolds (mvcc.stateAfter σ.log) cm); mvcc.api.mvccTxn t γ trace (.read σ) ∗
      traceutil.ownTrace trace te }}

abbrev txn.api.applyCompares.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (sl : GoSlice)
    (cps : List Loc) (cms : List CmpModel),
  {{ pkgInit ∗ mvcc.api.mvccTxn t γ trace (.read σ) ∗ traceutil.ownTrace trace te ∗
      ⌜txn.api.Reach σ⌝ ∗ sl ↦*□ cps ∗ txn.comparesIs cps cms }}
    (App (App (Val (@! txn.applyCompares)) (Val #t)) (Val #sl))
  {{ RET #(cms.all (cmpHolds (mvcc.stateAfter σ.log))); mvcc.api.mvccTxn t γ trace (.read σ) ∗
      traceutil.ownTrace trace te }}

abbrev txn.api.compareToPath.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (rt : Loc)
    (tm : TxnModel),
  {{ pkgInit ∗ mvcc.api.mvccTxn t γ trace (.read σ) ∗ traceutil.ownTrace trace te ∗
      ⌜txn.api.Reach σ⌝ ∗ txn.txnRequestIs rt tm }}
    (App (App (Val (@! txn.compareToPath)) (Val #t)) (Val #rt))
  {{ (sl : GoSlice), RET #sl; mvcc.api.mvccTxn t γ trace (.read σ) ∗ traceutil.ownTrace trace te ∗
      sl ↦* txn.txnPath (mvcc.stateAfter σ.log) tm ∗ ownSliceCap Bool sl (DFrac.own 1) }}

/-- `getPrevKV(trace, txnWrite, p)` at a transaction of either kind (its state `mstate k`).
(The trace kept at `te`, here and in `checkAndGetPrevKV`, `checkPut`, `checkTxn`: gap E's `∃ te'`
superseded, decided by the coordinator, 2026-11-05: traceutil's `StepWithFunction` keeps the flag;
`notes/mvcc-migration/txn.md` gap E.) -/
abbrev txn.api.getPrevKV.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (k : MTxn) (p : Loc) (o : OpFull),
  {{ pkgInit ∗ ⌜trace ≠ null⌝ ∗ mvcc.api.mvccTxn t γ trace k ∗ traceutil.ownTrace trace te ∗
      ⌜txn.api.Reach k.state⌝ ∗ txn.putRequestIs p o }}
    (App (App (App (Val (@! txn.getPrevKV)) (Val #trace)) (Val #t)) (Val #p))
  {{ (r : Loc), RET (PairV #r #(GoInterface.nil)); mvcc.api.mvccTxn t γ trace k ∗
      traceutil.ownTrace trace te ∗
      if txn.readsPrev o then txn.prevKvIs r (txn.api.mstate k) o.key else ⌜r = null⌝ }}

abbrev txn.api.checkAndGetPrevKV.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (k : MTxn) (p : Loc) (o : OpFull),
  {{ pkgInit ∗ ⌜trace ≠ null⌝ ∗ mvcc.api.mvccTxn t γ trace k ∗ traceutil.ownTrace trace te ∗
      ⌜txn.api.Reach k.state⌝ ∗ txn.putRequestIs p o }}
    (App (App (App (Val (@! txn.checkAndGetPrevKV)) (Val #trace)) (Val #t)) (Val #p))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); mvcc.api.mvccTxn t γ trace k ∗
      traceutil.ownTrace trace te ∗
      ((⌜err = GoInterface.nil⌝ ∗
          ⌜txn.needsPrev o = true → (mvcc.findKey o.key (txn.api.mstate k)).isSome⌝ ∗
          if txn.readsPrev o then txn.prevKvIs r (txn.api.mstate k) o.key else ⌜r = null⌝) ∨
       (⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (txn.api.mstate k) = none ∧ r = null⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err)) }}

abbrev txn.api.checkPut.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (k : MTxn) (le : GoInterface)
    (γl : GName) (p : Loc) (o : OpFull) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
  {{ pkgInit ∗ ⌜trace ≠ null⌝ ∗ mvcc.api.mvccTxn t γ trace k ∗ traceutil.ownTrace trace te ∗
      ⌜txn.api.Reach k.state⌝ ∗ txn.putRequestIs p o ∗ txn.isTxnLessor le γl ∗
      lease.lessorUser γl L I }}
    (App (App (App (App (Val (@! txn.checkPut)) (Val #trace)) (Val #t)) (Val #le)) (Val #p))
  {{ (err : GoInterface), RET #err; mvcc.api.mvccTxn t γ trace k ∗
      traceutil.ownTrace trace te ∗
      lease.lessorUser γl L I ∗
      ((⌜err = GoInterface.nil ∧
          (txn.needsPrev o = true → (mvcc.findKey o.key (txn.api.mstate k)).isSome)⌝ ∗
          txn.leaseOk L o.leaseID) ∨
       (⌜o.leaseID ≠ W64 0 ∧ o.leaseID ∉ L⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err) ∨
       (⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (txn.api.mstate k) = none⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err)) }}

abbrev txn.api.checkTxn.spec : Prop :=
  ∀ (tw : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (rt : Loc)
    (t : TxnModel) (le : GoInterface) (γl : GName) (pl : GoSlice) (rest : List Bool)
    (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (lu : Bool),
  (lu = false → txn.txnReadonly t = true) →
  {{ pkgInit ∗ ⌜trace ≠ null⌝ ∗ mvcc.api.mvccTxn tw γ trace (.read σ) ∗
      traceutil.ownTrace trace te ∗ ⌜txn.api.Reach σ⌝ ∗ txn.txnRequestIs rt t ∗
      txn.isTxnLessor le γl ∗ (⌜lu = false⌝ ∨ lease.lessorUser γl L I) ∗
      pl ↦*□ (txn.txnPath (mvcc.stateAfter σ.log) t ++ rest) }}
    (App (App (App (App (App (Val (@! txn.checkTxn)) (Val #trace)) (Val #tw)) (Val #rt)) (Val #le))
      (Val #pl))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); mvcc.api.mvccTxn tw γ trace (.read σ) ∗
      traceutil.ownTrace trace te ∗ (⌜lu = false⌝ ∨ lease.lessorUser γl L I) ∗
      ((⌜err = GoInterface.nil ∧ n = W64 (txn.nestedCount (mvcc.stateAfter σ.log) t : Int) ∧
          txn.PathsIgnOk (mvcc.stateAfter σ.log)
            (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t))⌝ ∗
        txn.leasesOk L (txn.opsLeases (mvcc.stateAfter σ.log)
          (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t)))) ∨
       (⌜err ≠ GoInterface.nil ∧ n = W64 0 ∧
          (txn.txnLeased t → ¬ (txn.PathsIgnOk (mvcc.stateAfter σ.log)
            (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t)) ∧ txn.PathsLeaseOk (mvcc.stateAfter σ.log) L
            (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t))))⌝ ∗ txn.checkErrIs err)) }}

/-- `executeRange(ctx, lg, txnRead, r, withTotalCount)` at a transaction of either kind:
`rangeResult` at the log and revision it reads. No sort premise: the sort's (`sortSmall`) comes
from its `Txn.Range` call's `stateOk` at the revision read (`srvPre_stateOk`, below). -/
abbrev txn.api.executeRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (tw : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (k : MTxn) (r : Loc) (o : OpFull)
    (withTotal : Bool),
  {{ pkgInit ∗ mvcc.api.mvccTxn tw γ trace k ∗ traceutil.ownTrace trace te ∗ mvcc.txnCtx ctx cd ∗
      (if nd then mvcc.neverDone cd else iprop(True)) ∗ traceutil.ctxTraceIs ctx (some trace) ∗
      txn.rangeRequestIs r o ∗
      ⌜txn.api.Reach k.state ∧ txn.validSortTarget o⌝ }}
    (App (App (App (App (App (Val (@! txn.executeRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #tw)) (Val #r)) (Val #withTotal))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      mvcc.api.mvccTxn tw γ trace k ∗ traceutil.ownTrace trace te ∗
      txn.rangeResult resp err k.readLog k.readRev k.state.crev o withTotal ∗ txn.rangeHdr resp err ∗
      ⌜nd = true → err = GoInterface.nil ∨ sint.Z k.readRev < sint.Z o.base.rev ∨
        sint.Z (mvcc.rangeRev k.readRev o.base.rev) < k.state.crev⌝ }}

/-- `put(ctx, txnWrite, p, prevKV)` at a write transaction begun at `σ` with `pend` pending. -/
abbrev txn.api.put.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (tw : GoInterface) (γ : MvccName)
    (trace : Loc) (te : Bool) (σ : MvccState) (pend : List mvcc.Change) (p : Loc) (o : OpFull)
    (prev : Loc) (L : List w64),
  {{ pkgInit ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx (some trace) ∗
      mvcc.api.mvccTxn tw γ trace (.write σ pend) ∗ traceutil.ownTrace trace te ∗
      txn.putRequestIs p o ∗
      (if txn.readsPrev o then txn.prevKvIs prev (txn.pendState σ.log pend) o.key
        else ⌜prev = null⌝) ∗
      ⌜txn.needsPrev o = true → (mvcc.findKey o.key (txn.pendState σ.log pend)).isSome⌝ ∗
      txn.leaseOk L (txn.putLeaseOf o (mvcc.findKey o.key (txn.pendState σ.log pend))) ∗
      lease.leaseOwn (mvccLeases γ) L (mvcc.pendItems σ.log pend) }}
    (App (App (App (App (Val (@! txn.put)) (Val #(GoInterface.ok ctx))) (Val #tw)) (Val #p))
      (Val #prev))
  {{ (resp : Loc), RET #resp;
      mvcc.api.mvccTxn tw γ trace
        (.write σ (pend ++ [txn.putChangeOf o (mvcc.findKey o.key (txn.pendState σ.log pend))])) ∗
      traceutil.ownTrace trace te ∗
      txn.putResponseIs resp (W64 (σ.log.length : Int))
        (if o.base.prevKV then mvcc.findKey o.key (txn.pendState σ.log pend) else none) ∗
      txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) ∗
      lease.leaseOwn (mvccLeases γ) L (mvcc.pendItems σ.log
        (pend ++ [txn.putChangeOf o (mvcc.findKey o.key (txn.pendState σ.log pend))])) }}

/-- `deleteRange(ctx, txnWrite, dr)` at a write transaction begun at `σ` with `pend` pending. -/
abbrev txn.api.deleteRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (tw : GoInterface)
    (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (pend : List mvcc.Change) (dr : Loc)
    (o : OpFull) (L : List w64),
  {{ pkgInit ∗ mvcc.txnCtx ctx cd ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      mvcc.api.mvccTxn tw γ trace (.write σ pend) ∗ traceutil.ownTrace trace te ∗
      ⌜txn.api.Reach σ⌝ ∗ txn.deleteRangeRequestIs dr o ∗
      lease.leaseOwn (mvccLeases γ) L (mvcc.pendItems σ.log pend) }}
    (App (App (App (Val (@! txn.deleteRange)) (Val #(GoInterface.ok ctx))) (Val #tw)) (Val #dr))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); traceutil.ownTrace trace te ∗
      ((⌜err = GoInterface.nil⌝ ∗
        mvcc.api.mvccTxn tw γ trace (.write σ (pend ++ txn.delChanges (txn.pendState σ.log pend) o)) ∗
        txn.deleteRangeResponseIs resp
          (W64 ((mvcc.writeRev σ.log (pend ++ txn.delChanges (txn.pendState σ.log pend) o) : Nat) :
            Int))
          (rangeIn (txn.pendState σ.log pend) o).length
          (if o.base.prevKV then rangeIn (txn.pendState σ.log pend) o else []) ∗
        txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
        lease.leaseOwn (mvccLeases γ) L
          (mvcc.pendItems σ.log (pend ++ txn.delChanges (txn.pendState σ.log pend) o))) ∨
      (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
        mvcc.api.mvccTxn tw γ trace (.write σ pend) ∗
        lease.leaseOwn (mvccLeases γ) L (mvcc.pendItems σ.log pend))) }}

/-- `executeTxn(ctx, lg, txnWrite, rt, txnPath, tresp, skip)` at a transaction `k`: a write one
(begun at `σ`, `pend` pending), or (`k.isRead`) the read-only wrapper of a read transaction at
`σ`. No size premise (each get's sort from its range's `stateOk`). -/
abbrev txn.api.executeTxn.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (γ : MvccName) (trace : Loc) (te : Bool) (tw : GoInterface) (k : MTxn) (rt : Loc)
    (t : TxnModel) (pl : GoSlice) (rest : List Bool) (tresp : Loc) (skip : Bool) (L : List w64),
  let s0 := mvcc.stateAfter k.state.log
  let ops := t.branch (txn.txnOk s0 t)
  let run := txn.srvOps s0 (W64 (k.state.log.length : Int)) (txn.api.mstate k) ops
  {{ pkgInit ∗ mvcc.api.mvccTxn tw γ trace k ∗ traceutil.ownTrace trace te ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some trace) ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      txn.txnRequestIs rt t ∗ pl ↦*□ (txn.txnPath s0 t ++ rest) ∗ txn.respsSkel s0 tresp ops ∗
      txn.leasesOk L (txn.opsLeases s0 ops) ∗
      (if txn.api.MTxn.isRead k then iprop(True) else txn.leasesKnown L (txn.api.mstate k)) ∗
      (⌜txn.api.MTxn.isRead k = true⌝ ∨ lease.leaseOwn (mvccLeases γ) L (mvcc.pendItems k.state.log k.pend)) ∗
      ⌜txn.api.Reach k.state ∧
        txn.OpsOk false s0 (W64 (k.state.log.length : Int)) (txn.api.mstate k) ops ∧
        (txn.api.MTxn.isRead k = true → ∀ op ∈ ops, txn.opIsGet op = true) ∧
        (nd = false → txn.api.MTxn.isRead k = true)⌝ }}
    (App (App (App (App (App (App (App (Val (@! txn.executeTxn)) (Val #(GoInterface.ok ctx)))
      (Val #lg)) (Val #tw)) (Val #rt)) (Val #pl)) (Val #tresp)) (Val #skip))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); traceutil.ownTrace trace te ∗
      ((⌜err = GoInterface.nil ∧ n = W64 (txn.nestedCount s0 t : Int) ∧
            (txn.api.MTxn.isRead k = true → run.1 = [])⌝ ∗
        mvcc.api.mvccTxn tw γ trace (txn.api.MTxn.append k run.1) ∗
        txn.respsIs skip tresp ops run.2 ∗
        (if txn.api.MTxn.isRead k then iprop(True)
         else txn.leasesKnown L (txn.api.mstate (txn.api.MTxn.append k run.1))) ∗
        (⌜txn.api.MTxn.isRead k = true⌝ ∨ lease.leaseOwn (mvccLeases γ) L
          (mvcc.pendItems k.state.log (k.pend ++ run.1)))) ∨
      (⌜nd = false⌝ ∗ mvcc.errorfIs err ∗ mvcc.api.mvccTxn tw γ trace k ∗ txn.roRespsRd tresp)) }}

set_option linter.iris.dupNamespace false in
/-- `txn(ctx, lg, txnWrite, rt, isWrite, txnPath, skip)` on a fresh write transaction begun at `σ`
(`isWrite`), or the read-only wrapper of a read transaction at `σ`. (Superseded 2026-11-05, decided
by the coordinator: `σ.pending = none` only for a write, `notes/mvcc-migration/txn.md` gap D.) -/
abbrev txn.api.txn.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (γ : MvccName) (trace : Loc) (te : Bool) (tw : GoInterface) (ro : Bool) (σ : MvccState)
    (rt : Loc) (t : TxnModel) (pl : GoSlice) (skip : Bool) (L : List w64),
  let k : MTxn := if ro then .read σ else .write σ []
  let chs := txn.api.txnChs σ.log t
  {{ pkgInit ∗ mvcc.api.mvccTxn tw γ trace k ∗ traceutil.ownTrace trace te ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some trace) ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      txn.txnRequestIs rt t ∗ pl ↦*□ txn.txnPath (mvcc.stateAfter σ.log) t ∗
      txn.leasesOk L (txn.opsLeases (mvcc.stateAfter σ.log)
        (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t))) ∗
      (if ro then iprop(True) else txn.leasesKnown L (mvcc.stateAfter σ.log)) ∗
      (⌜ro = true⌝ ∨ lease.leaseOwn (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter σ.log))) ∗
      ⌜txn.api.Reach σ ∧ (ro = false → σ.pending = none) ∧
        txn.OpsOk false (mvcc.stateAfter σ.log) (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log)
          (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t)) ∧
        (ro = true → txn.txnReadonly t = true) ∧ (nd = false → ro = true ∧ lg ≠ null)⌝ }}
    (App (App (App (App (App (App (App (Val (@! txn.txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #tw)) (Val #rt)) (Val #(!ro))) (Val #pl)) (Val #skip))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); traceutil.ownTrace trace te ∗
      ((⌜err = GoInterface.nil ∧ (ro = true → chs = [])⌝ ∗
        mvcc.api.mvccTxn tw γ trace (txn.api.MTxn.append k chs) ∗
        txn.txnResponseIs skip resp (W64 (mvcc.writeRev σ.log chs : Int)) t
          (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).1
          (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
        (if ro then iprop(True) else
          txn.leasesKnown L (mvcc.applyChanges (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) chs)) ∗
        (⌜ro = true⌝ ∨ lease.leaseOwn (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.applyChanges
          (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) chs)))) ∨
      (⌜nd = false⌝ ∗ mvcc.errorfIs err ∗ mvcc.api.mvccTxn tw γ trace k ∗
        txn.txnRespShell resp ∗ txn.roTxnRespRd resp ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp))) }}

end spec

/-! ## The sort's premise from `Txn.Range`'s `stateOk` (pure; proved)

`txn.kvOk` (non-negative values) goes, unified with the API's `kvSortOk` (round 16: positive values,
stronger). The comparators (`kvSortBy*__Less`, `sortRangeResults`) need only non-negative values (Go's
`(a - b) < 0` is the signed order for values in `[0, 2^63)`), so they take `kvSortOk` and weaken by
`kvSortOk_nonneg`; the direction every lemma needs is `kvSortOk → (≥ 0)`. `sortSmall` is restated
over `kvSortOk` (`sortSmallA`); `stateAt_small` and `sortSmall_of_sortOk` (from `LogSmall`) have no
user left in txn and go. -/

section sortpure
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

theorem txn.api.kvSortOk_nonneg (v : EtcdKv) (h : mvcc.api.kvSortOk v) :
    0 ≤ sint.Z v.version ∧ 0 ≤ sint.Z v.createRev ∧ 0 ≤ sint.Z v.modRev := by
  unfold mvcc.api.kvSortOk at h; omega

/-- `sortSmall` over the API's values' predicate. -/
def txn.api.sortSmallA (o : OpFull) (s : List EtcdKv) : Prop :=
  (o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2) →
    (txn.srvPre o s).length ≤ 2 ^ 62 ∧ ∀ v ∈ txn.srvPre o s, mvcc.api.kvSortOk v

/-- **The sort's premise from a range's `stateOk`** (today's `srvPre_small`, at `kvSortOk`). -/
theorem txn.api.srvPre_stateOk (o : OpFull) (st : List EtcdKv) (h : mvcc.api.stateOk st) :
    txn.api.sortSmallA o st := by
  intro _
  unfold txn.srvPre
  split
  · simp
  · have hin : (rangeIn st o).length ≤ st.length := List.length_filter_le _ _
    have htk : ∀ (lim : Option Nat) (l : List EtcdKv), (mvcc.takeLimit lim l).length ≤ l.length := by
      intro lim l; cases lim <;> simp [mvcc.takeLimit]; omega
    have hmem : ∀ (lim : Option Nat) (l : List EtcdKv) (x : EtcdKv), x ∈ mvcc.takeLimit lim l → x ∈ l := by
      intro lim l x hx; cases lim with
      | none => exact hx
      | some n => exact List.mem_of_mem_take hx
    refine ⟨?_, ?_⟩
    · have := List.length_filter_le (kvFilterOk o)
        ((mvcc.takeLimit (mvcc.limitOf (txn.rangeLimitOf o)) (rangeIn st o)).map
          (txn.kvRead (txn.fastKeysOnly o)))
      have := htk (mvcc.limitOf (txn.rangeLimitOf o)) (rangeIn st o)
      have := h.1
      simp only [List.length_map] at *
      omega
    · intro v hv
      obtain ⟨hv, _⟩ := List.mem_filter.1 hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      have hw' := h.2 w (List.mem_filter.1 (hmem _ _ _ hw)).1
      unfold txn.kvRead; split <;> exact hw'

/-- **The shared lemma** (txn and the server; for `ApiState`, xreview §11): a transaction begun at
`log` has the item map of the state after `log`. -/
theorem txn.api.pendItems_nil (log : mvcc.Log) :
    mvcc.pendItems log [] = mvcc.leaseItemsOf (mvcc.stateAfter log) := rfl

end sortpure

end EtcdGrove
end Perennial
