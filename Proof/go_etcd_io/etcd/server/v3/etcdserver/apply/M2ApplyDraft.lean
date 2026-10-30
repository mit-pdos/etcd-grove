/-
**M2, the apply side: the apply package's compaction arm (Draft)** (`notes/m2-apply-plan.md`).
Imported by nothing but the server's apply-side Draft; no `axiom`, no `sorry`; nothing switched.
Each `…D` is the draft of the unsuffixed statement it names, to replace it in place at the switch.

- **The premise on the request's kind** (`dispatchOkD`): `dispatchOk` without its compaction
  conjunct; by the mode (`dispatchOkM cmp`, review round 1's S-1: `dispatchOk` itself stays, so the
  off texts read as today, `dispatchOkM_false`).
- **The compaction revision** the apply thread holds the right at: `cmpRevAfter` (the store's
  `updateCompactRev`: raised to `rev` when above), `chainCompacts` (the chains whose `Compaction`
  reaches the backend: every wrapper but the corrupt applier passes it on, `corrupt.go`),
  `dispatchCrev`/`applyCrev` (what `dispatch`/`Apply` do to it).
- **The apply thread's compaction resources** (`cmpOwn E c`): by the store's mode
  (`kbCmpM E.γ.kb`, the backend-keyed reading, as `srvKVCloserM`), the store's restorable compaction
  right at `c` (`mvcc.compactRightR`, at least `-1`), else `c = -1`; and the write-back supply
  (`mvcc.kbWTSupplyM`, persistent: the server's from its write budget's stock, R2-7/Q4 (a)).
- **What a compaction needs** (`cmpAdmitRev`, `cmpAdmit`): the store compacting and the revision
  one of the log's (`rev < log.length`). No `NoDelPutAt` (review round 1's F-5: the items are
  stated in the fork fix's form, etcd-io/etcd#22377 being in the fork since 2026-10-28; the switch
  waits for mvcc's specs to drop the premise).
- **The answers** (`cmpRespOk`, `cmpAnswerIs`, `dispatchAnswerD`, `dispatchResultD`,
  `applyResultIsD`): the compaction's error arm with no trace (F-2: `EtcdServer.Compact` reads
  `result.Trace` before `result.Err`).
- **The statements** (drafts of the linked ones): mvcc's `store.updateCompactRev.specD` and
  `store.Compact.specD` (F-1: no `ErrFutureRev` arm, unreachable under their precondition, and no
  `NoDelPutAt`), the chain's `Compaction` triple (`cmpTriple`, a conjunct to add to
  `applierTriples`), `applierV3backend.Compaction.specD` (new: the method has no spec today),
  `uberApplier.dispatch.specD`, `uberApplier.Apply.specD`, `apply.Apply.specRecD` (S-1).
- **Glue, proved**: `cmp_store_pre` (the backend's `Compaction` can meet `store.Compact.spec`'s
  precondition from its own: the right and the supply from `cmpOwn`, the certificate and the
  writer's fragment from `kvOwn`, the reader's token lent by `writerOwn`, the hook's facts from the
  options), `dispatchOkD_of`, `dispatchOkM_false`, `dispatchOkM_of`, `cmpRevAfter_ge`/
  `dispatchCrev_ge` (the revision never goes down), `dispatchCrev_nonCmp`, `cmpAdmit_nonCmp`,
  `dispatchAnswerD_nonCmp`, `cmp_not_future` (F-1's argument: the store's committed log extends a
  caller's certificate, so `rev < log.length` excludes `ErrFutureRev`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyRec

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

namespace apply

/-! ## The pure part -/

/-- **`dispatchOk` in compaction mode** (`InvUber.lean`'s, which stays as it is: review round 1's
S-1; the mode-indexed `dispatchOkM` picks it on): some field set,
`AuthEnable` only with auth on; a compaction is admitted (M2: compaction in the model). -/
def dispatchOkD (on : Bool) (rq : IRRModel) : Prop :=
  dispatchKind rq ≠ .none ∧ (dispatchKind rq = .authEnable → on = true)

theorem dispatchOkD_of (on : Bool) (rq : IRRModel) (h : dispatchOk on rq) : dispatchOkD on rq :=
  ⟨h.2.1, h.2.2⟩

/-- **The premise on the request's kind, by the cluster's compaction mode** (review round 1's S-1,
in place of redefining `dispatchOk`): today's `dispatchOk` off, `dispatchOkD` (a compaction
admitted) on. Used where the mode is known: the server's shapes (`rqShapeD cmp`, so `kvWorkD`
and the invariant), the apply thread's premise (`entryOkMD on cmp`), the uber's specs at `E.cmp`. -/
def dispatchOkM (cmp on : Bool) (rq : IRRModel) : Prop :=
  if cmp then dispatchOkD on rq else dispatchOk on rq

/-- **Off, today's** (by definition: every compaction-off text reads as today). -/
theorem dispatchOkM_false (on : Bool) (rq : IRRModel) : dispatchOkM false on rq = dispatchOk on rq :=
  rfl

theorem dispatchOkM_of (cmp on : Bool) (rq : IRRModel) (h : dispatchOk on rq) :
    dispatchOkM cmp on rq := by
  unfold dispatchOkM; split
  · exact dispatchOkD_of on rq h
  · exact h

/-- **The chains whose `Compaction` reaches the backend**: the auth, quota and capped wrappers pass
it on (they do not override it), the corrupt applier answers `ErrCorrupt` (`corrupt.go`). -/
def chainCompacts : Chain → Bool
  | .backend => true
  | .auth _ c => chainCompacts c
  | .quota c => chainCompacts c
  | .capped c => chainCompacts c
  | .corrupt _ => false

/-- **The compaction revision after `Compact(rev)`** at `crev` (`updateCompactRev`): `rev` when
above, else unchanged (`ErrCompacted`). -/
def cmpRevAfter (crev : Int) (rev : w64) : Int :=
  if crev < sint.Z rev then sint.Z rev else crev

theorem cmpRevAfter_ge (crev : Int) (rev : w64) : crev ≤ cmpRevAfter crev rev := by
  unfold cmpRevAfter; split <;> omega

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

/-- **What `Apply` does to the compaction revision**: a dispatched request's `dispatchCrev`; a
skipped or rejected one nothing. -/
def applyCrev (rq : IRRModel) (v3 : Bool) (c : Chain) (crev : Int) : ApplyOut → Int
  | .dispatched _ _ => dispatchCrev c rq v3 crev
  | _ => crev

/-- **What a compaction at `rev` needs at the log `log`** (pure; written once, review round 1's
S-8): the store compacting (its backend in compaction mode: the KV invariant admits compaction
entries only in the cluster's compaction mode, and `envAgree`/`srvEnvOkD` tie the store's mode to
it) and the revision one of the log's (the committed log's claim, `cmpLogOk`). No `NoDelPutAt`:
the fork has etcd-io/etcd#22377 (review round 1's F-5; mvcc's specs drop the premise before the
switch). -/
def cmpAdmitRev (kb : Option mvcc.KBReal) (log : mvcc.Log) (rev : w64) : Prop :=
  mvcc.kbCmpM kb ∧ sint.Z rev < log.length

/-- **What a compaction request needs at the log `log`**: `cmpAdmitRev` at its revision; nothing
for another kind. -/
def cmpAdmit (kb : Option mvcc.KBReal) (log : mvcc.Log) (rq : IRRModel) : Prop :=
  dispatchKind rq = .compaction → ∀ r, rq.compaction = some r → cmpAdmitRev kb log r

theorem cmpAdmit_nonCmp (kb : Option mvcc.KBReal) (log : mvcc.Log) (rq : IRRModel)
    (h : dispatchKind rq ≠ .compaction) : cmpAdmit kb log rq := fun h' => absurd h' h

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The apply thread's compaction resources -/

/-- **The store's compaction right at `c`, by the mode**: a compacting store's restorable right
(`mvcc.compactRightR`: half the compaction revision's authority, the jobs' queue, the closer's and
the jobs' shares of the fields), at least `-1`; a store that does not compact, none, at `-1`. -/
def cmpRight (E : AEnv GF) (c : Int) : IProp GF :=
  if mvcc.kbCmpM E.γ.kb then iprop(mvcc.compactRightR E.s E.γ c ∗ ⌜-1 ≤ c⌝) else iprop(⌜c = -1⌝)

/-- **The apply thread's compaction resources at `c`**: the right by the mode and the compaction's
write-back supply (persistent; `True` off). -/
def cmpOwn (E : AEnv GF) (c : Int) : IProp GF :=
  iprop(cmpRight E c ∗ mvcc.kbWTSupplyM E.γ.kb)

theorem cmpOwn_off (E : AEnv GF) (c : Int) (h : ¬ mvcc.kbCmpM E.γ.kb) :
    cmpOwn (GF := GF) E c ⊢ ⌜c = -1⌝ := by
  unfold cmpOwn cmpRight
  simp only [h, ↓reduceIte]
  iintro ⟨%hc, -⟩
  ipureintro; exact hc

theorem cmpOwn_ge (E : AEnv GF) (c : Int) : cmpOwn (GF := GF) E c ⊢ ⌜-1 ≤ c⌝ := by
  unfold cmpOwn cmpRight
  split
  · iintro ⟨⟨-, %h⟩, -⟩; ipureintro; exact h
  · iintro ⟨%h, -⟩; ipureintro; omega

/-! ## The answers -/

/-- **A successful compaction's response** `rp` at the log `log` (owned: `EtcdServer.Compact`
writes it): its header, owned, at the current revision (`Compaction`'s last lines,
`KV.Range(ctx, "compaction", …)` at the latest revision: `rr.Rev`). -/
def cmpRespOk (log : mvcc.Log) (rp : Loc) : IProp GF :=
  iprop(⌜rp ≠ null⌝ ∗ ∃ cv : etcdserverpb.CompactionResponse, rp ↦ cv ∗
    ∃ hv : etcdserverpb.ResponseHeader, cv.Header' ↦ hv ∗
      ⌜hv.Revision' = W64 ((log.length : Int) - 1)⌝)

/-- **The answer of the chain `c`'s `Compaction(rev)`** at the log `log` and the compaction revision
`crev`: through a chain that reaches the backend, a response at the current revision with its trace
(`rev` above `crev`), or `ErrCompacted` with no response and no trace (`rev` at or below `crev`); the
corrupt applier's `ErrCorrupt`. The channel (`Physc`) is not stated: the request path reads it only
of a physical compaction, which the proposers never send (`compactReqIs`). -/
def cmpAnswerIs (c : Chain) (log : mvcc.Log) (crev : Int) (rev : w64) (resp : Loc) (ch : GoChan)
    (trace : Loc) (err : GoInterface) : IProp GF :=
  if chainCompacts c then
    iprop((⌜crev < sint.Z rev ∧ err = GoInterface.nil⌝ ∗ cmpRespOk log resp ∗ traceRes trace) ∨
      (⌜sint.Z rev ≤ crev ∧ resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err))
  else
    iprop(⌜resp = null ∧ ch = chan.nil ∧ trace = null⌝ ∗
      txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt err)

/-- **Draft of `dispatchAnswer`** (`InvUber.lean`), with the result's trace `tr` (review round 1's
F-2): today's, with the compaction's case (today `True`, a compaction being out of the model): a
`*pb.CompactionResponse` interface value, a response at the current revision without an error, or,
with one, no response and **no trace** (`backend.go:73-75`; `EtcdServer.Compact` reads
`result.Trace` before `result.Err`, `v3_server.go:393-401`, so its proof needs the trace `nil` on an
error: what `compactResultIs` gives today). `dispatchResult` already gives `applyErrIs` of every
error. -/
def dispatchAnswerD (rq : IRRModel) (log : mvcc.Log) (skip : Bool) (resp err : GoInterface)
    (tr : Loc) (o : Outcome) : IProp GF :=
  if dispatchKind rq = .compaction then
    iprop(∃ rp : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.CompactionResponse.ty) #rp⌝ ∗
      ((⌜err = GoInterface.nil⌝ ∗ cmpRespOk log rp) ∨
        ⌜rp = null ∧ err ≠ GoInterface.nil ∧ tr = null⌝))
  else dispatchAnswer rq log skip resp err o

theorem dispatchAnswerD_nonCmp (rq : IRRModel) (log : mvcc.Log) (skip : Bool)
    (resp err : GoInterface) (tr : Loc) (o : Outcome) (h : dispatchKind rq ≠ .compaction) :
    dispatchAnswerD (GF := GF) rq log skip resp err tr o = dispatchAnswer rq log skip resp err o := by
  unfold dispatchAnswerD; simp only [h, ↓reduceIte]

/-- **Draft of `dispatchResult`** (`InvUber.lean`): today's, over `dispatchAnswerD` (the result's
trace passed). -/
def dispatchResultD (rq : IRRModel) (v3 : Bool) (log : mvcc.Log) (skip : Bool) (ar : Loc)
    (o : Outcome) : IProp GF :=
  if preV3Kind (dispatchKind rq) = true ∨ v3 = true then
    iprop(⌜ar ≠ null⌝ ∗ ∃ v : Result, ar ↦□ v ∗ dispatchAnswerD rq log skip v.Resp' v.Err' v.Trace' o ∗
      applyErrIs v.Err')
  else iprop(⌜ar = null⌝)

/-- **Draft of `applyResultIs`** (`InvUber.lean`), over `dispatchResultD`. -/
def applyResultIsD (rq : IRRModel) (v3 : Bool) (log : mvcc.Log) (ar : Loc) : ApplyOut → IProp GF
  | .skipped => iprop(⌜ar = null⌝)
  | .rejected => rejectedResultIs ar
  | .dispatched o skip => dispatchResultD rq v3 log skip ar o

/-! ## The statements -/

/-- **The chain `c`'s `Compaction` triple** (draft; a conjunct to add to `applierTriples`, the
methods `dispatch` calls): `Compaction(cr)` for the request's `*pb.CompactionRequest` `cr` at the
revision `rev` (`compactionIs`), admitted (`cmpAdmit`'s facts at `rev`), with the apply thread's KV
at `log` and the critical-section contract (`mPre`: `store.Compact`'s `SetScheduledCompact` writes
under the batch lock), and its compaction resources at `crev`: the KV and the chain's resources as
they were, the contract's `Post` or `Pre`, the compaction resources at the revision after it
(`cmpRevAfter crev rev` through a chain that reaches the backend), the answer (`cmpAnswerIs`).
Its proof for the backend rests on `store.Compact.specD` (F-1: no `ErrFutureRev` arm, which
`cmpAnswerIs` has no case for). -/
def cmpTriple (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ (cr : Loc) (rev : w64) (log : mvcc.Log) (crev : Int) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ compactionIs cr rev ∗ ⌜cmpAdmitRev E.γ.kb log rev⌝ ∗
          mPre E c (.ok ai) info log Pre Q Post ∗ cmpOwn E crev }}
        (App (Val #(methods ai.ty go!"Compaction" ai.v)) (Val #cr))
      {{ (resp : Loc) (ch : GoChan) (trace : Loc) (err : GoInterface),
          RET (PairV (PairV (PairV #resp #ch) #trace) #err);
          kvOwn E log ∗ chainRes c (.ok ai) info ∗ (Post ∨ Pre) ∗
          cmpOwn E (if chainCompacts c then cmpRevAfter crev rev else crev) ∗
          cmpAnswerIs c log crev rev resp ch trace err }}))

instance cmpTriple_persistent (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) :
    Persistent (cmpTriple E c ai) := by
  unfold cmpTriple; infer_instance

end defs

/-! ## The glue: `store.Compact`'s precondition from the backend's -/

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The backend's `Compaction` meets `store.Compact.spec`'s precondition** (the glue of
`applierV3backend.Compaction.specD` over `mvcc_store_Compact`, the resource part): from the apply
thread's KV (`kvOwn`), its compaction resources (`cmpOwn`, on) and the options' hook fact
(`backendOptsOk`'s `hookOk`), the store's restorable right at `crev` (at least `-1`), the KV's
certificate of its log, the writer's hook (`hookIs`: the hook's facts and the writer's fragment,
from `txn.kvWriter`), the store's reader token (lent by `writerOwn`), the supply; and back, at the
compaction revision `store.Compact` leaves (any `c'` at least `-1`). -/
theorem cmp_store_pre (E : AEnv GF) (log : mvcc.Log) (crev : Int) (h : mvcc.kbCmpM E.γ.kb) :
    kvOwn E log ∗ cmpOwn E crev ∗ mvcc.hookOk E.γ E.P E.f ⊢
      mvcc.compactRightR E.s E.γ crev ∗ ⌜-1 ≤ crev⌝ ∗ mvcc.idxCert E.γ.idx log ∗
      mvcc.hookIs E.γ E.P E.f ∗ mvcc.storeRT E.γ ∗ mvcc.kbWTSupplyM E.γ.kb ∗
      (∀ c' : Int, mvcc.compactRightR E.s E.γ c' -∗ ⌜-1 ≤ c'⌝ -∗ mvcc.hookIs E.γ E.P E.f -∗
        mvcc.storeRT E.γ -∗ kvOwn E log ∗ cmpOwn E c') := by
  iintro ⟨Hkv, Hc, #Hhk⟩
  ihave ⟨Hkv, #Hcert⟩ := kvOwn_cert E log $$ Hkv
  iunfold kvOwn at Hkv
  icases Hkv with ⟨Hsr, Hw, Hll, Hrd, Hwo⟩
  iunfold txn.kvWriter at Hw
  icases Hw with ⟨Hsw, Hwl, Hfr⟩
  ihave ⟨Hrt, Hwob⟩ := mvcc.writerOwn_rt E.γ $$ Hwo
  iunfold cmpOwn at Hc
  icases Hc with ⟨Hr, #Hsup⟩
  iunfold cmpRight at Hr
  simp only [h, ↓reduceIte]
  icases Hr with ⟨Hr, %hge⟩
  iframe Hr Hcert Hrt Hsup
  isplitr
  · ipureintro; exact hge
  isplitl [Hfr]
  · iunfold mvcc.hookIs; iframe Hhk Hfr
  iintro %c' Hr' %hc' Hhi Hrt'
  iunfold mvcc.hookIs at Hhi
  icases Hhi with ⟨-, Hfr'⟩
  ihave Hwo := Hwob $$ Hrt'
  isplitl [Hsr Hsw Hwl Hfr' Hll Hrd Hwo]
  · iunfold kvOwn
    iframe Hsr Hll Hrd Hwo
    iunfold txn.kvWriter
    iframe Hsw Hwl Hfr'
  iunfold cmpOwn
  iframe Hsup
  iunfold cmpRight
  simp only [h, ↓reduceIte]
  iframe Hr'
  ipureintro; exact hc'

/-- **F-1's argument** (why `store.Compact.specD` and `store.updateCompactRev.specD` can drop the
`ErrFutureRev` arm, for the mvcc Probe): in that branch the store holds its committed log's
authority (`revMuBody`'s `idxLogAuth γ.idx (revQ γ q) log`), which extends the caller's certificate
(`idxLogAuth_cert_prefix`), so a revision of the caller's log is one of the committed log's: the
branch's `rev > currentRev = |log| - 1` is contradictory. -/
theorem cmp_not_future (γ : mvcc.IdxNames) (q : Qp) (ilog log : mvcc.Log) (rev : w64) :
    mvcc.idxLogAuth (GF := GF) γ q ilog ∗ mvcc.idxCert γ log ⊢
      ⌜sint.Z rev < log.length → sint.Z rev < ilog.length⌝ := by
  iintro H
  ihave %h := mvcc.idxLogAuth_cert_prefix γ q ilog log $$ H
  ipureintro
  intro hr
  have := h.length_le
  omega

end glue

end apply

/-! ## The drafted specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **Draft of `store.updateCompactRev.spec`** (review round 1's F-1, G6; an mvcc statement, which
`store.Compact.spec`, exported as `mvcc_store_Compact`, is written over): today's without the
`ErrFutureRev` arm (unreachable under the precondition: `cmp_not_future`) and without the
`NoDelPutAt` premise (F-5: etcd-io/etcd#22377 is in the fork; `compactJobPre` and `crevSafe` lose
it with the re-proof of the compaction job). -/
abbrev mvcc.store.updateCompactRev.specD : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (hk : Option val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length⌝ ∗
      mvcc.lockCtxM γ P hk Pre Q Post ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.store.ty @!!
      go!"updateCompactRev")) (Val #rev))
  {{ (ch : GoChan) (prev : w64) (err : GoInterface), RET (PairV (PairV #ch #prev) #err);
      mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗
      ((⌜err = GoInterface.nil ∧ ch = chan.nil ∧ prev = W64 c ∧ c < sint.Z rev⌝ ∗
        mvcc.muInvAt s γ 1 (sint.Z rev) ∗ mvcc.compactRightR s γ (sint.Z rev) ∗ Post ∗
        mvcc.compactJobPre s γ rev) ∨
      (⌜sint.Z rev ≤ c ∧ prev = W64 0⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□
          GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True))) }}

/-- **Draft of `store.Compact.spec`** (review round 1's F-1, G6; exported as `mvcc_store_Compact`):
today's without the `ErrFutureRev` arm (unreachable: the caller's certificate is of a log with
`rev`, which the committed log extends, `cmp_not_future`; the docstring already said so) and without
the `NoDelPutAt` premise (F-5: etcd-io/etcd#22377 in the fork, the re-proof of `keyIndex.doCompact`
and of the job against the fixed code). Two answers: compacted at `rev`, or `ErrCompacted`. -/
abbrev mvcc.store.Compact.specD : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log) (te : Bool),
  trace ≠ null → mvcc.storeCmp γ → -1 ≤ c →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length⌝ ∗
      mvcc.hookIs γ P f ∗
      mvcc.csContract P f Pre Q Post ∗ traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗
      mvcc.kbWTSupplyM γ.kb }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.store.ty @!!
      go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err);
      traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗ mvcc.hookIs γ P f ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRightR s γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□
          GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True))) }}

/-- **`a.Compaction(cr)`** on the `*applierV3backend` `p` (draft; no spec today, the method being
out of the model): `EnsureTrace` makes a fresh trace (`context.TODO()` holds none), `KV.Compact(trace,
rev)` (the watchable store's embedded `*store`'s, `store.Compact.specD`: the right, the certificate
of a log with `rev`, the hook, the contract, the reader's token, the supply), then, on
success, `KV.Range(ctx, "compaction", nil, {})` at the latest revision (a latest read is never
compacted: `rr` is not nil) for the response's header. The chain-`.backend` instance of
`cmpTriple`. -/
abbrev apply.applierV3backend.Compaction.specD : Prop :=
  ∀ (E : AEnv GF) (p cr : Loc) (rev : w64) (log : mvcc.Log) (crev : Int) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.backendIs E p ∗ apply.compactionIs cr rev ∗ ⌜apply.cmpAdmitRev E.γ.kb log rev⌝ ∗
      apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log
        Pre Q Post ∗ apply.cmpOwn E crev }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"Compaction")) (Val #cr))
  {{ (resp : Loc) (ch : GoChan) (trace : Loc) (err : GoInterface),
      RET (PairV (PairV (PairV #resp #ch) #trace) #err);
      apply.kvOwn E log ∗ (Post ∨ Pre) ∗ apply.cmpOwn E (apply.cmpRevAfter crev rev) ∗
      apply.cmpAnswerIs .backend log crev rev resp ch trace err }}

/-- **Draft of `uberApplier.dispatch.spec`**: today's, with the compaction arm: `dispatchOkM E.cmp`
(a compaction admitted in compaction mode only; off, today's `dispatchOk`), the compaction's facts
(`cmpAdmit`), the apply thread's compaction resources at `crev` in, at `dispatchCrev c rq v3 crev`
out, and the compaction's answer (`dispatchResultD`; at the switch `dispatchAnswer` itself gains the
case and the trace). `dispatchStep`
needs no change: a compaction is not a `storeKind`, so the log is unchanged (true: a compaction
changes no value at a revision it keeps). -/
abbrev apply.uberApplier.dispatch.specD : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (opts : ApplierOptions) (c : apply.Chain) (a : GoInterface)
    (r : Loc) (rq : IRRModel) (skip v3 : Bool) (log F : mvcc.Log) (Pre Q Post : IProp GF)
    (rs : apply.RestM) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.chainRes c a info ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a ∗ apply.applierSpec E c a ∗
      apply.kvOwn E log ∗ apply.certPreV v3 E c rq log ∗ mvcc.storeWT E.γ ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
      ⌜apply.rqOk log rq ∧ apply.dispatchOkM E.cmp E.authOn rq ∧ apply.cmpAdmit E.γ.kb log rq⌝ ∗
      ⌜c.authOn = E.authOn⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ apply.cmpOwn E crev }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"dispatch")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; apply.chainResAny c a ∗ E.FS ∗ E.RO (apply.restAfter rq v3 rs) ∗
      apply.cmpOwn E (apply.dispatchCrev c rq v3 crev) ∗
      ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep c rq v3 log o ∧ apply.chainAfter rq v3 c c' ∧
          apply.kvFloorOk rq v3 F log o ∧ a' = a ∧ c' = c⌝ ∗
        (∀ _ : v3 = true, apply.chainClass E.authMode info c rq o) ∗
        apply.resTrace ar ∗ apply.dispatchResultD rq v3 log skip ar o }}

/-- **Draft of `uberApplier.Apply.spec`**: today's, with the compaction arm threaded as in
`dispatch.specD` (`dispatchOkM E.cmp`, `cmpAdmit`, `cmpOwn` in at `crev` and out at
`applyCrev rq v3 x.chain crev out`, `applyResultIsD`). `apply.Apply.spec` is parametric in its method's contract and
does not change. -/
abbrev apply.uberApplier.Apply.specD : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (opts : ApplierOptions) (x : apply.ApplyKV) (r : Loc)
    (rq : IRRModel) (skip v3 : Bool) (F : mvcc.Log) (Pre Q Post : IProp GF) (rs : apply.RestM)
    (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗
      apply.certPreV v3 E x.chain rq x.log ∗
      mvcc.storeWT E.γ ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
      ⌜apply.rqOk x.log rq ∧ apply.dispatchOkM E.cmp E.authOn rq ∧ apply.cmpAdmit E.γ.kb x.log rq⌝ ∗
      ⌜skip = true → rq.txn.isSome = true⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ apply.cmpOwn E crev }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; E.FS ∗ ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
      apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
      E.RO (apply.restOut rq v3 out rs) ∗ apply.cmpOwn E (apply.applyCrev rq v3 x.chain crev out) ∗
      ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip) ∧
        apply.applyFloorOk rq v3 F x.log out⌝ ∗
      apply.resTrace ar ∗ apply.applyResultIsD rq v3 x.log ar out ∗
      apply.applyAuthRes E.authMode x.chain rq v3 out }}

/-- **Draft of `apply.Apply.specRec`** (`ApplyRec.lean`; review round 1's S-1: `applyEntryNormal`'s
proof calls `Apply` through it): today's, with the compaction arm threaded as in
`uberApplier.Apply.specD` (`dispatchOkM E.cmp`, `cmpAdmit`, `cmpOwn` in at `crev` and out at
`applyCrev`, `applyResultIsD`; at the switch the revision is `x.crev` and `cmpOwn` part of
`applyKV`, A1). -/
abbrev apply.Apply.specRecD : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (F : mvcc.Log) (rs : apply.RestM)
    (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.applierFor ua E ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post))
       else iprop(True)) ∗ Pre ∗
      apply.applyKV E ua x ∗ mvcc.storeWT E.γ ∗ apply.certPreV v3 E x.chain rq x.log ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.rqOk x.log rq ∧
        apply.dispatchOkM E.cmp E.authOn rq ∧ apply.cmpAdmit E.γ.kb x.log rq⌝ ∗
      mvcc.idxCert E.γ.idx F ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ apply.cmpOwn E crev }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗ E.FS ∗
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ apply.resTrace ar ∗
      ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
        E.RO (apply.restOut rq v3 out rs) ∗
        apply.cmpOwn E (apply.applyCrev rq v3 x.chain crev out) ∗
        ⌜apply.applyStep rq v3 x x' out ∧ apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.applyResultIsD rq v3 x.log ar out ∗ apply.applyAuthRes E.authMode x.chain rq v3 out ∗
        (⌜out.waived = false⌝ ∨ G ot id) }}

end spec

end EtcdGrove
end Perennial
