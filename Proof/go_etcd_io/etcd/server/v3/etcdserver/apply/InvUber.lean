/-
The uber-applier and `apply.Apply` (`server/v3/etcdserver/apply`, `uber_applier.go`, `apply.go`):
the shared vocabulary of their specs. Lean-first (no Rocq counterpart); plan: `notes/decisions.md`,
"The server's apply" (unit 2).

**The uber-applier** (`*uberApplier` `p`): its fields `lg`, `alarmStore`, `warningApplyDuration`
and `applyV3base` are written once by `NewUberApplier` (`uberIs E p opts`, persistent: the
options' contracts `backendOptsOk E opts` and the base chain's applier `applierSpec E baseChain`);
its `applyV3` is the apply thread's (`uberOwn E p c`: the field and `applierSpec E c`), which
`restoreAlarms` rewrites with the chain the alarms ask for (`alarmChain on ns cr`, for whatever the
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

/-- The requests whose outcome is the chain's (`chainStep`): the KV requests, the lease
revocation (whose lessor deletes the lease's keys through the store) and (M2's apply side,
2026-10-31) the compaction (the corrupt applier rejects it). -/
def storeKind : ReqKind → Bool
  | .range | .put | .deleteRange | .txn | .leaseRevoke | .compaction => true
  | _ => false

/-- **The premise on the request's kind**: some field set (`dispatch` panics on a request with
none, its `default`: only a crafted WAL entry has none, unit 0's suspect 2), `AuthEnable` only
with auth on. A compaction is admitted (M2's apply side, the switch, 2026-10-31: item 1; until
then it was out of the model): its gate is the KV invariant's `plainLogM` by the cluster's mode and
its facts `cmpAdmit`. -/
def dispatchOk (on : Bool) (rq : IRRModel) : Prop :=
  dispatchKind rq ≠ .none ∧ (dispatchKind rq = .authEnable → on = true)

/-- **What `dispatch(rq, v3)` does to the KV** through the chain `c` at the log `log`. -/
def dispatchStep (c : Chain) (rq : IRRModel) (v3 : Bool) (log : mvcc.Log) (o : Outcome) : Prop :=
  if preV3Kind (dispatchKind rq) = true ∨ v3 = false then o = .applied log false
  else if storeKind (dispatchKind rq) = true then chainStep backendStep c rq log o
  else o.logAfter log = log

/-- The request kinds whose triples take a floor (the vertical slice's unit V2): the KV writes. -/
def isFloorKind : ReqKind → Bool
  | .put | .deleteRange | .txn => true
  | _ => false

/-- **The floor met by `dispatch(rq, v3)`** (unit V2): a KV write dispatched with `v3` whose
backend ran ran at a log extending the floor `F` (`floorOkO`). -/
def kvFloorOk (rq : IRRModel) (v3 : Bool) (F log : mvcc.Log) (o : Outcome) : Prop :=
  v3 = true → isFloorKind (dispatchKind rq) = true → floorOkO F log o

/-- The uber-applier's chain after `dispatch(rq, v3)`: the same, or after an alarm request
(`uberApplier.Alarm` calls `restoreAlarms` on an `ACTIVATE` or `DEACTIVATE`) the chain the alarm
store's answers ask for. -/
def chainAfter (rq : IRRModel) (v3 : Bool) (c c' : Chain) : Prop :=
  c' = c ∨ (v3 = true ∧ dispatchKind rq = .alarm ∧ ∃ ns cr, c' = alarmChain c.authOn ns cr)

/-- **The state `apply.Apply` changes**: the committed log of the KV, the uber-applier's
current chain, and the compaction revision `crev` the apply thread's compaction resources are at
(`cmpOwn`; M2's apply side, A1: `-1` at a store that does not compact). -/
structure ApplyKV where
  log : mvcc.Log
  chain : Chain
  crev : Int

/-- **What `dispatch(rq, v3)` through the chain `c` does to the compaction revision**: a compaction
dispatched with `v3` through a chain that reaches the backend raises it (`cmpRevAfter`); nothing
else changes it (without `v3` a compaction is not dispatched: `dispatch`'s
`if !shouldApplyV3 { return nil }`). -/
def dispatchCrev (c : Chain) (rq : IRRModel) (v3 : Bool) (crev : Int) : Int :=
  if v3 = true ∧ dispatchKind rq = .compaction ∧ chainCompacts c = true then
    match rq.compaction with
    | some r => cmpRevAfter crev r
    | none => crev
  else crev

theorem dispatchCrev_ge (c : Chain) (rq : IRRModel) (v3 : Bool) (crev : Int) :
    crev ≤ dispatchCrev c rq v3 crev := by
  unfold dispatchCrev
  split
  · split
    · exact cmpRevAfter_ge _ _
    · exact Int.le_refl _
  · exact Int.le_refl _

theorem dispatchCrev_nonCmp (c : Chain) (rq : IRRModel) (v3 : Bool) (crev : Int)
    (h : dispatchKind rq ≠ .compaction) : dispatchCrev c rq v3 crev = crev := by
  unfold dispatchCrev
  split
  · rename_i h'; exact absurd h'.2.1 h
  · rfl

theorem dispatchCrev_noV3 (c : Chain) (rq : IRRModel) (crev : Int) :
    dispatchCrev c rq false crev = crev := by
  unfold dispatchCrev; simp

/-- **What a compaction request needs at the log `log`**: `cmpAdmitRev` at its revision; nothing
for another kind. -/
def cmpAdmit (kb : Option mvcc.KBReal) (log : mvcc.Log) (rq : IRRModel) : Prop :=
  dispatchKind rq = .compaction → ∀ r, rq.compaction = some r → cmpAdmitRev kb log r

theorem cmpAdmit_nonCmp (kb : Option mvcc.KBReal) (log : mvcc.Log) (rq : IRRModel)
    (h : dispatchKind rq ≠ .compaction) : cmpAdmit kb log rq := fun h' => absurd h' h

/-- What became of an entry in `apply.Apply`. -/
inductive ApplyOut where
  /-- No waiter and no side effect (`noSideEffect`): not applied, `nil` result. -/
  | skipped
  /-- The auth layer's admin check failed (`needAdminPermission`): `&Result{Err: err}`. -/
  | rejected
  /-- Dispatched: the outcome `o`, the wrapper's `SkipRangeExecution` `skip`. -/
  | dispatched (o : Outcome) (skip : Bool)

/-- The outcome was **waived for want of a waiter** (`apply.Apply`'s `needResult` false: the
request not applied, `skipped`, or a transaction's ranges not run, `SkipRangeExecution`). -/
def ApplyOut.waived : ApplyOut → Bool
  | .skipped => true
  | .rejected => false
  | .dispatched _ skip => skip

/-- **What `apply.Apply` does to the rest buckets and the cluster's members** (D22, 2026-10-23):
a dispatched request's `restAfter`; a skipped or rejected one nothing. -/
def restOut [GooseExts] (rq : IRRModel) (v3 : Bool) : ApplyOut → RestM → RestM
  | .dispatched _ _, r => restAfter rq v3 r
  | _, r => r

/-- **What `apply.Apply` does with the request `rq`** (`v3`: `shouldApplyV3`) from the state `x`
to `x'`. -/
def applyStep (rq : IRRModel) (v3 : Bool) (x x' : ApplyKV) : ApplyOut → Prop
  | .skipped => noSideEffect rq = true ∧ x' = x
  | .rejected => needAdminPermission rq = true ∧ x' = x
  | .dispatched o skip => (skip = true → rq.txn.isSome = true) ∧
      dispatchStep x.chain rq v3 x.log o ∧ x'.log = o.logAfter x.log ∧
      chainAfter rq v3 x.chain x'.chain ∧ x'.crev = dispatchCrev x.chain rq v3 x.crev

/-- A request that is no compaction leaves the compaction revision. -/
theorem applyStep_crev_nonCmp (rq : IRRModel) (v3 : Bool) (x x' : ApplyKV) (out : ApplyOut)
    (h : dispatchKind rq ≠ .compaction) (hs : applyStep rq v3 x x' out) : x'.crev = x.crev := by
  cases out with
  | skipped => rw [hs.2]
  | rejected => rw [hs.2]
  | dispatched o sk => rw [hs.2.2.2.2]; exact dispatchCrev_nonCmp _ _ _ _ h

/-- **The floor met by `Apply(rq, v3)`** (unit V2): its dispatched outcome meets the floor
(`kvFloorOk`); a skipped or rejected request ran nothing. -/
def applyFloorOk (rq : IRRModel) (v3 : Bool) (F log : mvcc.Log) : ApplyOut → Prop
  | .dispatched o _ => kvFloorOk rq v3 F log o
  | _ => True

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
/-- **What `Apply`'s auth layer established of the request** (A3, 2026-10-23): dispatched with
`v3` (through the chain; without `v3` the KV requests are not run), the request's class through
the chain for its principal (`chainClass`: if the auth layer did not reject, the permissions the
request needs were granted to `principalOf rq`) and its admin check's pass (`adminPass`); rejected
by that check, or skipped, nothing. -/
def applyAuthRes (M : auth.AuthMode) (c : Chain) (rq : IRRModel) (v3 : Bool) :
    ApplyOut → IProp GF
  | .dispatched o _ =>
      iprop((∀ _ : v3 = true, chainClass M (principalOf rq) c rq o) ∗ adminPass M c rq)
  | _ => iprop(True)

instance applyAuthRes_persistent (M : auth.AuthMode) (c : Chain) (rq : IRRModel) (v3 : Bool)
    (out : ApplyOut) : Persistent (applyAuthRes (GF := GF) M c rq v3 out) := by
  unfold applyAuthRes; split <;> infer_instance


/-! ## The uber-applier in the heap -/

/-- **The base applier `a`'s auth layer** (the auth plan's E3k, 2026-10-27; persistent): an
`*authApplierV3` `pa` (`authIs`) over an applier of the quota-over-backend chain, its `as` and
`lessor` fields the options' auth store and lessor: what its KV triples at the latest state
(`applierKVL_auth`, E2y) are built from (`uberKVL_of_base`). -/
def baseAuth (E : AEnv GF) (opts : ApplierOptions) (a : GoInterface) : IProp GF :=
  iprop(∃ (pa : Loc) (inner : GoInterface),
    ⌜a = interface.mkOk (go.GoType.PointerType authApplierV3.ty) #pa⌝ ∗ authIs E pa inner ∗
    applierSpec E (.quota .backend) inner ∗
    structFieldRef authApplierV3 go!"as" pa ↦□ opts.AuthStore' ∗
    structFieldRef authApplierV3 go!"lessor" pa ↦□ opts.Lessor')

instance baseAuth_persistent (E : AEnv GF) (opts : ApplierOptions) (a : GoInterface) :
    Persistent (baseAuth E opts a) := by
  unfold baseAuth; infer_instance

/-- **The `*uberApplier` `p`, persistently**: the fields `NewUberApplier` wrote from the options
`opts` (whose contracts hold in `E`), the base chain's applier (`newApplierV3`'s). -/
def uberIs (E : AEnv GF) (p : Loc) (opts : ApplierOptions) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ backendOptsOk E opts ∗
    structFieldRef uberApplier go!"lg" p ↦□ opts.Logger' ∗
    structFieldRef uberApplier go!"alarmStore" p ↦□ opts.AlarmStore' ∗
    structFieldRef uberApplier go!"warningApplyDuration" p ↦□ opts.WarningApplyDuration' ∗
    ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
      applierSpec E (baseChain E.authOn) base ∗
      -- (the auth plan's E2m) its shape, for its admin triples (`applierAdmin_baseX`)
      baseShape opts base ∗
      -- (the auth plan's E3k) its auth layer, for its KV triples at the latest state
      baseAuth E opts base)

instance uberIs_persistent (E : AEnv GF) (p : Loc) (opts : ApplierOptions) :
    Persistent (uberIs E p opts) := by
  unfold uberIs; infer_instance

/-- **The current applier's shape** (the auth plan's E2o, 2026-10-26; persistent): the chain
`c` is `restoreAlarms`' for some alarms (`alarmChain`), and the applier `a` is the base applier
(`applyV3base`) wrapped as those alarms ask (`alarmShape`), what `applierAdmin_curG`
(`AdminChain.lean`) needs to lift the base's admin triples to it. `dispatch` never changes the
current applier (no alarm request is admitted, `rqOk`), so this is fixed after `NewUberApplier`. -/
def uberShape (E : AEnv GF) (p : Loc) (c : Chain) (a : GoInterface) : IProp GF :=
  iprop(∃ (base : GoInterface) (ns cr : Bool), ⌜c = alarmChain E.authOn ns cr⌝ ∗
    structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗ alarmShape ns cr base a)

instance uberShape_persistent (E : AEnv GF) (p : Loc) (c : Chain) (a : GoInterface) :
    Persistent (uberShape E p c a) := by
  unfold uberShape; infer_instance

/-- **The uber-applier `p`'s current applier**, the apply thread's: its `applyV3` field, an
applier of the chain `c`, with its shape (`uberShape`). -/
def uberOwn (E : AEnv GF) (p : Loc) (c : Chain) : IProp GF :=
  iprop(∃ a : GoInterface, structFieldRef uberApplier go!"applyV3" p ↦ a ∗ applierSpec E c a ∗
    ⌜c.authOn = E.authOn⌝ ∗ uberShape E p c a)

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
`x.chain`, the KV resources at the committed log `x.log`, and the compaction resources at
`x.crev` (`cmpOwn`; M2's apply side, A1). -/
def applyKV (E : AEnv GF) (ua : GoInterface) (x : ApplyKV) : IProp GF :=
  iprop(∃ p : Loc, ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗
    uberOwn E p x.chain ∗ kvOwn E x.log ∗ cmpOwn E x.crev)

/-! ## The results -/

/-- `ar` is an `*apply.Result` whose `Err` can be read (nil: no result), an error `errors.Is`
can take (`applyErrIs`): what the server's apply thread reads of it (`applyEntryNormal`; its own
`resultOk`, the same definition, went in the apply package's unit 3). -/
def resultErrOk (ar : Loc) : IProp GF :=
  iprop(⌜ar = null⌝ ∨
    ∃ err : GoInterface, structFieldRef Result go!"Err" ar ↦□ err ∗ applyErrIs err)

instance resultErrOk_persistent (ar : Loc) : Persistent (resultErrOk (GF := GF) ar) := by
  unfold resultErrOk; infer_instance

/-- **The answer in `dispatch`'s result** to `rq` at `log` (`resp`, `err`: the `Result`'s `Resp`
and `Err`), for the outcome `o`: a KV request's or a revocation's, unit 1's outcome predicates
at the response's pointer; a request of the first `switch`, no response and no error; an
admin request the mode `on` admits (`adminKindOk`; E3w, 2026-10-27), a response of its type (what
its entry point asserts); the others, nothing (the triples of `applierSpec` say nothing of their
answers). A compaction's (M2's apply side, item 2): a `*pb.CompactionResponse`, owned without
an error (`cmpRespOk`), or with one, no response and no trace `tr`, the error mvcc's `ErrCompacted`
or, with the corrupt applier's rejection, `ErrCorrupt` (so the apply thread's NOSPACE check fails)
(`backend.go`: `EtcdServer.Compact`
reads `result.Trace` before `result.Err`). -/
def dispatchAnswer (rq : IRRModel) (log : mvcc.Log) (skip : Bool) (resp err : GoInterface)
    (tr : Loc) (o : Outcome) : IProp GF :=
  match dispatchKind rq with
  | .compaction => iprop(∃ rp : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.CompactionResponse.ty) #rp⌝ ∗
      ((⌜err = GoInterface.nil⌝ ∗ cmpRespOk rp) ∨
        (⌜rp = null ∧ err ≠ GoInterface.nil ∧ tr = null⌝ ∗
          (txn.errVarIs go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted err ∨
            (⌜o = .rejected .corrupt⌝ ∗
              txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt err)))))
  | .put => iprop(∃ (op : OpFull) (r : Loc), ⌜rq.put = some op ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.PutResponse.ty) #r⌝ ∗
      putAnswerIs log op r err o)
  | .deleteRange => iprop(∃ (op : OpFull) (r : Loc), ⌜rq.deleteRange = some op ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeResponse.ty) #r⌝ ∗
      deleteAnswerIs log op r err o)
  | .range => iprop(∃ (op : OpFull) (r : Loc), ⌜rq.range = some op ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.RangeResponse.ty) #r⌝ ∗
      rangeOutcomeIs log op r err o)
  | .txn => iprop(∃ (t : TxnModel) (r : Loc), ⌜rq.txn = some t ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.TxnResponse.ty) #r⌝ ∗
      txnAnswerIs log t skip r err o)
  | .leaseRevoke => iprop(∃ r : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeResponse.ty) #r⌝ ∗
      revokeOutcomeIs r err o)
  | .clusterVersionSet | .clusterMemberAttrSet | .downgradeInfoSet | .downgradeVersionTest =>
      iprop(⌜resp = GoInterface.nil ∧ err = GoInterface.nil⌝)
  | .authEnable => iprop(∃ r : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.AuthEnableResponse.ty) #r⌝)
  | .authUserAdd => iprop(∃ r : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.AuthUserAddResponse.ty) #r⌝)
  | .authRoleAdd => iprop(∃ r : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.AuthRoleAddResponse.ty) #r⌝)
  | .authUserGrantRole => iprop(∃ r : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.AuthUserGrantRoleResponse.ty) #r⌝)
  | .authRoleGrantPermission => iprop(∃ r : Loc, ⌜resp =
      interface.mkOk (go.GoType.PointerType etcdserverpb.AuthRoleGrantPermissionResponse.ty) #r⌝)
  | _ => iprop(True)

/-- **Without an error the answer does not depend on the trace** (only a compaction's error arm
names it). -/
theorem dispatchAnswer_nil_tr (rq : IRRModel) (log : mvcc.Log) (skip : Bool) (resp : GoInterface)
    (tr tr' : Loc) (o : Outcome) :
    dispatchAnswer (GF := GF) rq log skip resp GoInterface.nil tr o ⊢
      dispatchAnswer rq log skip resp GoInterface.nil tr' o := by
  unfold dispatchAnswer
  cases dispatchKind rq <;> simp only [] <;> try (iintro H; iexact H)
  iintro ⟨%rp, %h, (⟨%he, Hr⟩ | ⟨%h', -⟩)⟩
  · iexists rp
    isplitr
    · ipureintro; exact h
    ileft; iframe Hr
  · exact absurd rfl h'.2.1

/-- **`dispatch`'s result** `ar`: without `v3`, `nil` (but for the first `switch`'s requests);
else a fresh `Result`, read-only from then on, holding the answer, whose error `errors.Is` can
take (`applyErrIs`). -/
def dispatchResult (rq : IRRModel) (v3 : Bool) (log : mvcc.Log) (skip : Bool) (ar : Loc)
    (o : Outcome) : IProp GF :=
  if preV3Kind (dispatchKind rq) = true ∨ v3 = true then
    iprop(⌜ar ≠ null⌝ ∗ ∃ v : Result, ar ↦□ v ∗ dispatchAnswer rq log skip v.Resp' v.Err' v.Trace' o ∗
      applyErrIs v.Err')
  else iprop(⌜ar = null⌝)

/-- **The trace of `dispatch`'s result** `ar` (unit P1b, 2026-10-14): owned (`traceRes`), unless
the result is `nil` or an error (`raftRequest` reads the trace only of a result without error).
The apply thread hands it, with the result, to the goroutine serving the request. -/
def resTrace (ar : Loc) : IProp GF :=
  iprop(⌜ar = null⌝ ∨ ∃ v : Result, ar ↦□ v ∗ (⌜v.Err' ≠ GoInterface.nil⌝ ∨ traceRes v.Trace'))

theorem resTrace_of (ar : Loc) (v : Result) :
    ar ↦□ v ⊢ traceRes (GF := GF) v.Trace' -∗ resTrace ar := by
  iintro #H Ht
  unfold resTrace
  iright
  iexists v
  iframe H
  iright; iexact Ht

theorem resTrace_err (ar : Loc) (v : Result) (h : v.Err' ≠ GoInterface.nil) :
    ar ↦□ v ⊢ resTrace (GF := GF) ar := by
  iintro #H
  unfold resTrace
  iright
  iexists v
  iframe H
  ileft; ipureintro; exact h

theorem resTrace_null : ⊢ resTrace (GF := GF) null := by
  unfold resTrace; iintro; ileft; ipureintro; rfl

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
