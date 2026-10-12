/-
The uber-applier and `apply.Apply` (`server/v3/etcdserver/apply`, `uber_applier.go`, `apply.go`):
the shared vocabulary of their specs. Lean-first (no Rocq counterpart); plan: `notes/decisions.md`,
"The server's apply" (unit 2).

**The uber-applier** (`*uberApplier` `p`): its fields `lg`, `alarmStore`, `warningApplyDuration`
and `applyV3base` are written once by `NewUberApplier` (`uberIs E p opts`, persistent: the
options' contracts `backendOptsOk E opts` and the base chain's applier `applierSpec E baseChain`);
its `applyV3` is the apply thread's (`uberOwn E p c`: the field and `applierSpec E c`), which
`restoreAlarms` rewrites with the chain the alarms ask for (`alarmChain ns cr`, for whatever the
alarm store answers). `applierFor ua E` is the persistent part at the `UberApplier` interface
value `ua`; `applyKV E ua x` the apply thread's part with its KV resources (`kvOwn E x.log`), at
`x : ApplyKV` (the committed log and the current chain).

**What `dispatch` does with a request** (`dispatchStep c rq v3 log o`, by `dispatchKind rq`): the
cluster requests and `DowngradeVersionTest` leave the KV as it is (whatever `v3`); without `v3`
nothing else runs (`nil` result); with it the KV requests and the lease revocation come to an
outcome of the chain (`chainStep backendStep c`), the others leave the log as it is. Its result
(`dispatchResult`): a fresh `Result` holding the method's answer (`dispatchAnswer`: unit 1's
outcome predicates at the response's pointer), or `nil` without `v3`.

**What `apply.Apply` does with an entry** (`applyStep rq v3 x x' out`, `out : ApplyOut`): skipped
(no waiter and no side effect: `nil`), rejected by the auth layer's admin check (`rejected`, the
state as it is), or dispatched (`dispatched o skip`: `dispatchStep` on `x`, the chain changed only
by an alarm request); its result `applyResultIs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3


namespace apply

/-! ## The request kinds, purely -/

/-- The requests `dispatch` handles before it looks at `shouldApplyV3` (its first `switch`). -/
def preV3Kind : ReqKind → Bool
  | .clusterVersionSet | .clusterMemberAttrSet | .downgradeInfoSet | .downgradeVersionTest => true
  | _ => false

/-- The requests whose outcome is the chain's (`chainStep`): the KV requests and the lease
revocation (whose lessor deletes the lease's keys through the store). -/
def storeKind : ReqKind → Bool
  | .range | .put | .deleteRange | .txn | .leaseRevoke => true
  | _ => false

/-- **The premise on the request's kind**: not a compaction (out of the model:
`notes/decisions.md`) and some field set (`dispatch` panics on a request with none, its
`default`: only a crafted WAL entry has none, unit 0's suspect 2). -/
def dispatchOk (rq : IRRModel) : Prop :=
  dispatchKind rq ≠ .compaction ∧ dispatchKind rq ≠ .none

/-- **What `dispatch(rq, v3)` does to the KV** through the chain `c` at the log `log`. -/
def dispatchStep (c : Chain) (rq : IRRModel) (v3 : Bool) (log : mvcc.Log) (o : Outcome) : Prop :=
  if preV3Kind (dispatchKind rq) = true ∨ v3 = false then o = .applied log false
  else if storeKind (dispatchKind rq) = true then chainStep backendStep c rq log o
  else o.logAfter log = log

/-- The uber-applier's chain after `dispatch(rq, v3)`: the same, or after an alarm request
(`uberApplier.Alarm` calls `restoreAlarms` on an `ACTIVATE` or `DEACTIVATE`) the chain the alarm
store's answers ask for. -/
def chainAfter (rq : IRRModel) (v3 : Bool) (c c' : Chain) : Prop :=
  c' = c ∨ (v3 = true ∧ dispatchKind rq = .alarm ∧ ∃ ns cr, c' = alarmChain ns cr)

/-- **The state `apply.Apply` changes**: the committed log of the KV and the uber-applier's
current chain. -/
structure ApplyKV where
  log : mvcc.Log
  chain : Chain

/-- What became of an entry in `apply.Apply`. -/
inductive ApplyOut where
  /-- No waiter and no side effect (`noSideEffect`): not applied, `nil` result. -/
  | skipped
  /-- The auth layer's admin check failed (`needAdminPermission`): `&Result{Err: err}`. -/
  | rejected
  /-- Dispatched: the outcome `o`, the wrapper's `SkipRangeExecution` `skip`. -/
  | dispatched (o : Outcome) (skip : Bool)

/-- **What `apply.Apply` does with the request `rq`** (`v3`: `shouldApplyV3`) from the state `x`
to `x'`. -/
def applyStep (rq : IRRModel) (v3 : Bool) (x x' : ApplyKV) : ApplyOut → Prop
  | .skipped => noSideEffect rq = true ∧ x' = x
  | .rejected => needAdminPermission rq = true ∧ x' = x
  | .dispatched o skip => (skip = true → rq.txn.isSome = true) ∧
      dispatchStep x.chain rq v3 x.log o ∧ x'.log = o.logAfter x.log ∧
      chainAfter rq v3 x.chain x'.chain

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The uber-applier in the heap -/

/-- **The `*uberApplier` `p`, persistently**: the fields `NewUberApplier` wrote from the options
`opts` (whose contracts hold in `E`), the base chain's applier (`newApplierV3`'s). -/
def uberIs (E : AEnv GF) (p : Loc) (opts : ApplierOptions) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ backendOptsOk E opts ∗
    structFieldRef uberApplier go!"lg" p ↦□ opts.Logger' ∗
    structFieldRef uberApplier go!"alarmStore" p ↦□ opts.AlarmStore' ∗
    structFieldRef uberApplier go!"warningApplyDuration" p ↦□ opts.WarningApplyDuration' ∗
    ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
      applierSpec E baseChain base)

instance uberIs_persistent (E : AEnv GF) (p : Loc) (opts : ApplierOptions) :
    Persistent (uberIs E p opts) := by
  unfold uberIs; infer_instance

/-- **The uber-applier `p`'s current applier**, the apply thread's: its `applyV3` field, an
applier of the chain `c`. -/
def uberOwn (E : AEnv GF) (p : Loc) (c : Chain) : IProp GF :=
  iprop(∃ a : GoInterface, structFieldRef uberApplier go!"applyV3" p ↦ a ∗ applierSpec E c a)

/-- **The `UberApplier` `ua`** (`apply.Apply`'s, the server's `uberApply`): an `*uberApplier`
in the environment `E` (persistent). The server's contract for its applier (`InvApplier.lean`),
whose batch lock's invariant and hook are `E.P` and `E.f`. -/
def applierFor (ua : GoInterface) (E : AEnv GF) : IProp GF :=
  iprop(∃ (p : Loc) (opts : ApplierOptions),
    ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗ uberIs E p opts)

instance applierFor_persistent (ua : GoInterface) (E : AEnv GF) :
    Persistent (applierFor ua E) := by
  unfold applierFor; infer_instance

/-- **The apply thread's applier state** at `x`: the `UberApplier` `ua`'s current chain
`x.chain` and the KV resources at the committed log `x.log`. -/
def applyKV (E : AEnv GF) (ua : GoInterface) (x : ApplyKV) : IProp GF :=
  iprop(∃ p : Loc, ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗
    uberOwn E p x.chain ∗ kvOwn E x.log)

/-! ## The results -/

/-- `ar` is an `*apply.Result` whose `Err` can be read (nil: no result), an error `errors.Is`
can take (`applyErrIs`): the server's `resultOk` (`InvApplier.lean`, which the apply package does
not import), the same definition. -/
def resultErrOk (ar : Loc) : IProp GF :=
  iprop(⌜ar = null⌝ ∨
    ∃ err : GoInterface, structFieldRef Result go!"Err" ar ↦□ err ∗ applyErrIs err)

instance resultErrOk_persistent (ar : Loc) : Persistent (resultErrOk (GF := GF) ar) := by
  unfold resultErrOk; infer_instance

/-- **The answer in `dispatch`'s result** to `rq` at `log` (`resp`, `err`: the `Result`'s `Resp`
and `Err`), for the outcome `o`: a KV request's or a revocation's, unit 1's outcome predicates
at the response's pointer; a request of the first `switch`, no response and no error; the others,
nothing (the triples of `applierSpec` say nothing of their answers). -/
def dispatchAnswer (rq : IRRModel) (log : mvcc.Log) (skip : Bool) (resp err : GoInterface)
    (o : Outcome) : IProp GF :=
  match dispatchKind rq with
  | .put => iprop(∃ (op : OpFull) (r : Loc), ⌜rq.put = some op ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.PutResponse.ty) #r⌝ ∗
      putOutcomeIs log op r err o)
  | .deleteRange => iprop(∃ (op : OpFull) (r : Loc), ⌜rq.deleteRange = some op ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeResponse.ty) #r⌝ ∗
      deleteOutcomeIs log op r err o)
  | .range => iprop(∃ (op : OpFull) (r : Loc), ⌜rq.range = some op ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.RangeResponse.ty) #r⌝ ∗
      rangeOutcomeIs log op r err o)
  | .txn => iprop(∃ (t : TxnModel) (r : Loc), ⌜rq.txn = some t ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.TxnResponse.ty) #r⌝ ∗
      txnOutcomeIs log t skip r err o)
  | .leaseRevoke => iprop(∃ r : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeResponse.ty) #r⌝ ∗
      revokeOutcomeIs r err o)
  | .clusterVersionSet | .clusterMemberAttrSet | .downgradeInfoSet | .downgradeVersionTest =>
      iprop(⌜resp = GoInterface.nil ∧ err = GoInterface.nil⌝)
  | _ => iprop(True)

/-- **`dispatch`'s result** `ar`: without `v3`, `nil` (but for the first `switch`'s requests);
else a fresh `Result`, read-only from then on, holding the answer, whose error `errors.Is` can
take (`applyErrIs`). -/
def dispatchResult (rq : IRRModel) (v3 : Bool) (log : mvcc.Log) (skip : Bool) (ar : Loc)
    (o : Outcome) : IProp GF :=
  if preV3Kind (dispatchKind rq) = true ∨ v3 = true then
    iprop(⌜ar ≠ null⌝ ∗ ∃ v : Result, ar ↦□ v ∗ dispatchAnswer rq log skip v.Resp' v.Err' o ∗
      applyErrIs v.Err')
  else iprop(⌜ar = null⌝)

/-- The result of the auth layer's admin rejection, read-only (`rejectResultIs`, persisted). -/
def rejectedResultIs (ar : Loc) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗ ∃ v : Result, ar ↦□ v ∗
    ⌜v.Err' ≠ GoInterface.nil ∧ v.Resp' = GoInterface.nil⌝ ∗ applyErrIs v.Err')

instance rejectedResultIs_persistent (ar : Loc) : Persistent (rejectedResultIs (GF := GF) ar) := by
  unfold rejectedResultIs; infer_instance

/-- **`apply.Apply`'s result** `ar` for the request `rq` at `log`, by what became of it. -/
def applyResultIs (rq : IRRModel) (v3 : Bool) (log : mvcc.Log) (ar : Loc) : ApplyOut → IProp GF
  | .skipped => iprop(⌜ar = null⌝)
  | .rejected => rejectedResultIs ar
  | .dispatched o skip => dispatchResult rq v3 log skip ar o

end defs

end apply
end EtcdGrove
end Perennial
