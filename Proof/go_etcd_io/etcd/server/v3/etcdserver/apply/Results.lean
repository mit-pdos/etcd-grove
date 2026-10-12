/-
The results of the server's apply package (`server/v3/etcdserver/apply`), restated at top level,
with the trust base of each printed in the build log (`#print axioms`). Each unit's results are
in a section of their own, in unit order (plan: `notes/decisions.md`, "The server's apply").

Unit 0 (translation and scaffolding) proved no function of the package; its `Link.lean` links
the trust-boundary axioms (`pbutil.MustUnmarshalMessage` per message type, semver, zap, the
txn package's loggers, prometheus, `context.WithValue`, the quota's constructor and `Cost`) and
imports the txn package's and mvcc's results the package calls (`Put`, `DeleteRange`, `Range`,
`Txn`, `store.Rev`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode

/-! ## Unit 1: the layers (`backend.go`, `quota.go`, `capped.go`, `corrupt.go`, `auth.go`)

Every function of the five files but the backend's `Compaction` (out of the model) has a
`Spec`/`Proof` pair and a linked result (`Link.lean`); the constructors package each layer's
triples into `applierSpec E c a` (`Chain.lean`), over the inner applier's. Restated here for the
chains the uber-applier builds (`alarmChain ns cr`: `baseChain` is `alarmChain false false`),
with the outcome relation `chainStep backendStep` computed in the txn package's terms:

* **A put** (`chain_put`): with a `CORRUPT` alarm `ErrCorrupt`; else with a `NOSPACE` alarm
  `ErrNoSpace`; else an auth error, or the backend's (`putModel`: the lease not found, or the
  ignore flag's key missing; else the one change `putChangeOf` committed, the client's put on
  `log`'s state: `txn.stateAfter_put`), after which the quota may answer `ErrNoSpace` (the put
  committed: `quotaAfter`).
* **A delete** (`chain_deleteRange`): the client's filter committed (`delChanges`), or the range
  read's error; no quota.
* **A range** (`chain_range`): `rangeResult` at `log`; nothing written.
* **A transaction** (`chain_txn`): `checkTxn`'s error, or the server's run `srvRunTxn`
  committed; with a `NOSPACE` alarm `ErrNoSpace` if it costs; the quota after it.
-/

/-- The quota's answer after the inner outcome `o'`: the same, or `ErrNoSpace` after a success
(the write committed). -/
def quotaAfter (o' o : Outcome) : Prop :=
  o = o' ∨ ∃ log', o' = .applied log' false ∧ o = .applied log' true

/-- **The backend's put** of `op` at the sole writer's log `log` (`txn.Put`, `put_soleWriter`):
the lease not found or the ignore flag's key missing (rejected, nothing written), or the one
change `putChangeOf` committed. -/
def putModel (op : OpFull) (log : mvcc.Log) (o : Outcome) : Prop :=
  (op.leaseID ≠ W64 0 ∧ o = .rejected .backend) ∨
  (txn.needsPrev op = true ∧ mvcc.findKey op.key (mvcc.stateAfter log) = none ∧
    o = .rejected .backend) ∨
  o = .applied (log ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter log))]]) false

/-- **The backend's delete** (`txn.DeleteRange`, `deleteRange_soleWriter`): the client's filter
committed, or (with `PrevKv`) the range read's error. -/
def deleteModel (op : OpFull) (log : mvcc.Log) (o : Outcome) : Prop :=
  o = .applied (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) op)) false ∨
  (op.base.prevKV = true ∧ o = .rejected .backend)

/-- **The backend's transaction** (`txn.Txn`, `txn_runTxn`): `checkTxn`'s error, or the server's
run `srvRunTxn` committed (nothing for a read-only request). -/
def txnModel (t : TxnModel) (log : mvcc.Log) (o : Outcome) : Prop :=
  o = .rejected .backend ∨
  (o = .applied (mvcc.commitLog log
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) false ∧
    (txn.txnReadonly t = true →
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 = []))

/-- A put through `alarmChain ns cr`. -/
def alarmPut (ns cr : Bool) (op : OpFull) (log : mvcc.Log) (o : Outcome) : Prop :=
  if cr then o = .rejected .corrupt
  else if ns then o = .rejected .noSpace
  else o = .rejected .auth ∨ ∃ o', putModel op log o' ∧ quotaAfter o' o

/-- A delete through `alarmChain ns cr`. -/
def alarmDelete (cr : Bool) (op : OpFull) (log : mvcc.Log) (o : Outcome) : Prop :=
  if cr then o = .rejected .corrupt
  else o = .rejected .auth ∨ deleteModel op log o

/-- A range through `alarmChain ns cr`. -/
def alarmRange (cr : Bool) (log : mvcc.Log) (o : Outcome) : Prop :=
  if cr then o = .rejected .corrupt
  else o = .rejected .auth ∨ o = .applied log false

/-- A transaction through `alarmChain ns cr`. -/
def alarmTxn (ns cr : Bool) (t : TxnModel) (log : mvcc.Log) (o : Outcome) : Prop :=
  if cr then o = .rejected .corrupt
  else (ns = true ∧ o = .rejected .noSpace) ∨ o = .rejected .auth ∨
    ∃ o', txnModel t log o' ∧ quotaAfter o' o

theorem chainStep_alarm_put (ns cr : Bool) (rq : IRRModel) (op : OpFull) (log : mvcc.Log)
    (o : Outcome) (hk : dispatchKind rq = .put) (hp : rq.put = some op)
    (h : chainStep backendStep (alarmChain ns cr) rq log o) : alarmPut ns cr op log o := by
  have hb : ∀ o', backendStep rq log o' → putModel op log o' := by
    intro o' h'
    unfold backendStep at h'
    rw [hk] at h'
    obtain ⟨op', hp', h'⟩ := h'
    rw [hp] at hp'; cases hp'
    exact h'
  have hbase : chainStep backendStep baseChain rq log o →
      o = .rejected .auth ∨ ∃ o', putModel op log o' ∧ quotaAfter o' o := by
    intro h
    simp only [baseChain, chainStep, authChecks, quotaChecks, hk, true_or, ↓reduceIte] at h
    rcases h with h | ⟨o', h', hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨o', hb o' h', hq⟩
  unfold alarmPut
  cases cr <;> cases ns <;>
    simp only [alarmChain, chainStep, corruptRejects, cappedRejects, hk, Bool.false_eq_true,
      ↓reduceIte] at h ⊢ <;> first | exact h | exact hbase h

theorem chainStep_alarm_delete (ns cr : Bool) (rq : IRRModel) (op : OpFull) (log : mvcc.Log)
    (o : Outcome) (hk : dispatchKind rq = .deleteRange) (hp : rq.deleteRange = some op)
    (h : chainStep backendStep (alarmChain ns cr) rq log o) : alarmDelete cr op log o := by
  have hb : backendStep rq log o → deleteModel op log o := by
    intro h'
    unfold backendStep at h'
    rw [hk] at h'
    obtain ⟨op', hp', h'⟩ := h'
    rw [hp] at hp'; cases hp'
    exact h'
  have hbase : chainStep backendStep baseChain rq log o →
      o = .rejected .auth ∨ deleteModel op log o := by
    intro h
    simp only [baseChain, chainStep, authChecks, quotaChecks, hk, true_or, ↓reduceIte,
      Bool.false_eq_true] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (hb h)
  unfold alarmDelete
  cases cr <;> cases ns <;>
    simp only [alarmChain, chainStep, corruptRejects, cappedRejects, hk, Bool.false_eq_true,
      ↓reduceIte, reduceCtorEq] at h ⊢ <;> first | exact h | exact hbase h

theorem chainStep_alarm_range (ns cr : Bool) (rq : IRRModel) (log : mvcc.Log)
    (o : Outcome) (hk : dispatchKind rq = .range)
    (h : chainStep backendStep (alarmChain ns cr) rq log o) : alarmRange cr log o := by
  have hbase : chainStep backendStep baseChain rq log o →
      o = .rejected .auth ∨ o = .applied log false := by
    intro h
    simp only [baseChain, chainStep, authChecks, quotaChecks, hk, true_or, ↓reduceIte,
      Bool.false_eq_true, backendStep] at h
    exact h
  unfold alarmRange
  cases cr <;> cases ns <;>
    simp only [alarmChain, chainStep, corruptRejects, cappedRejects, hk, Bool.false_eq_true,
      ↓reduceIte, reduceCtorEq] at h ⊢ <;> first | exact h | exact hbase h

theorem chainStep_alarm_txn (ns cr : Bool) (rq : IRRModel) (t : TxnModel) (log : mvcc.Log)
    (o : Outcome) (hk : dispatchKind rq = .txn) (hp : rq.txn = some t)
    (h : chainStep backendStep (alarmChain ns cr) rq log o) : alarmTxn ns cr t log o := by
  have hb : ∀ o', backendStep rq log o' → txnModel t log o' := by
    intro o' h'
    unfold backendStep at h'
    rw [hk] at h'
    obtain ⟨t', hp', h'⟩ := h'
    rw [hp] at hp'; cases hp'
    exact h'
  have hbase : chainStep backendStep baseChain rq log o →
      o = .rejected .auth ∨ ∃ o', txnModel t log o' ∧ quotaAfter o' o := by
    intro h
    simp only [baseChain, chainStep, authChecks, quotaChecks, hk, true_or, ↓reduceIte] at h
    rcases h with h | ⟨o', h', hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨o', hb o' h', hq⟩
  unfold alarmTxn
  cases cr <;> cases ns <;>
    simp only [alarmChain, chainStep, corruptRejects, cappedRejects, hk, Bool.false_eq_true,
      ↓reduceIte, true_and, false_and, false_or] at h ⊢
  all_goals first
    | exact h
    | exact Or.inr (hbase h)
    | exact hbase h
    | (rcases h with h | h
       · exact Or.inl h
       · exact Or.inr (hbase h))

section triples
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **A put through the uber-applier's chain** (`alarmChain ns cr`; `baseChain` at
`ns = cr = false`): the outcome `alarmPut` (the txn package's `putModel`), its answer, the log it
commits. -/
theorem chain_put (E : AEnv GF) (ns cr : Bool) (a : GoInterface) :
    applierSpec E (alarmChain ns cr) a ⊢
      ∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
      □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF),
        {{ putPre E (alarmChain ns cr) (.ok ai) r rq o log Pre Q Post }}
          (App (Val #(methods ai.ty go!"Put" ai.v)) (Val #r))
        {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
            ∃ oc : Outcome, ⌜alarmPut ns cr o log oc⌝ ∗ putAnswerIs log o resp err oc ∗
              kvOwn E (oc.logAfter log) ∗ chainRes (alarmChain ns cr) (.ok ai) ∗ (Post ∨ Pre) }}) := by
  iintro #Hs
  iunfold applierSpec at Hs
  icases Hs with ⟨%ai, %Ha, #Ht⟩
  iexists ai
  isplitr
  · ipureintro; exact Ha
  iunfold applierTriples at Ht
  icases Ht with ⟨#HPut, -⟩
  imodintro
  iintro %r %rq %o %log %Pre %Q %Post
  imodintro
  iintro %Φ Hpre HΦ
  iunfold putPre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hm⟩
  iapply HPut $$ %r %rq %o %log %Pre %Q %Post [Hm]
  · iunfold putPre
    iframe Hm Hr
    ipureintro; exact Hk
  inext
  iintro %resp %trace %err Hpost
  iapply HΦ
  iunfold kvPost at Hpost
  icases Hpost with ⟨%oc, %Hst, HR⟩
  iexists oc
  iframe HR
  ipureintro
  exact chainStep_alarm_put ns cr rq o log oc Hk.2.1 Hk.1 Hst
/-- **A delete through the uber-applier's chain** (`alarmChain ns cr`; `baseChain` at
`ns = cr = false`): the outcome `alarmDelete` (the txn package's `deleteModel`), its answer, the log it
commits. -/
theorem chain_deleteRange (E : AEnv GF) (ns cr : Bool) (a : GoInterface) :
    applierSpec E (alarmChain ns cr) a ⊢
      ∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
      □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF),
        {{ deletePre E (alarmChain ns cr) (.ok ai) r rq o log Pre Q Post }}
          (App (Val #(methods ai.ty go!"DeleteRange" ai.v)) (Val #r))
        {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
            ∃ oc : Outcome, ⌜alarmDelete cr o log oc⌝ ∗ deleteAnswerIs log o resp err oc ∗
              kvOwn E (oc.logAfter log) ∗ chainRes (alarmChain ns cr) (.ok ai) ∗ (Post ∨ Pre) }}) := by
  iintro #Hs
  iunfold applierSpec at Hs
  icases Hs with ⟨%ai, %Ha, #Ht⟩
  iexists ai
  isplitr
  · ipureintro; exact Ha
  iunfold applierTriples at Ht
  icases Ht with ⟨-, #HDel, -⟩
  imodintro
  iintro %r %rq %o %log %Pre %Q %Post
  imodintro
  iintro %Φ Hpre HΦ
  iunfold deletePre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hm⟩
  iapply HDel $$ %r %rq %o %log %Pre %Q %Post [Hm]
  · iunfold deletePre
    iframe Hm Hr
    ipureintro; exact Hk
  inext
  iintro %resp %trace %err Hpost
  iapply HΦ
  iunfold kvPost at Hpost
  icases Hpost with ⟨%oc, %Hst, HR⟩
  iexists oc
  iframe HR
  ipureintro
  exact chainStep_alarm_delete ns cr rq o log oc Hk.2.1 Hk.1 Hst
/-- **A range through the uber-applier's chain**: the outcome `alarmRange` (`rangeResult` at
`log` unless rejected), its answer; the log as it is. -/
theorem chain_range (E : AEnv GF) (ns cr : Bool) (a : GoInterface) :
    applierSpec E (alarmChain ns cr) a ⊢
      ∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
      □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log),
        {{ rangePre E (alarmChain ns cr) (.ok ai) r rq o log }}
          (App (Val #(methods ai.ty go!"Range" ai.v)) (Val #r))
        {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
            ∃ oc : Outcome, ⌜alarmRange cr log oc⌝ ∗ rangeOutcomeIs log o resp err oc ∗
              kvOwn E (oc.logAfter log) ∗ chainRes (alarmChain ns cr) (.ok ai) }}) := by
  iintro #Hs
  iunfold applierSpec at Hs
  icases Hs with ⟨%ai, %Ha, #Ht⟩
  iexists ai
  isplitr
  · ipureintro; exact Ha
  iunfold applierTriples at Ht
  icases Ht with ⟨-, -, #HRange, -⟩
  imodintro
  iintro %r %rq %o %log
  imodintro
  iintro %Φ Hpre HΦ
  iunfold rangePre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hm⟩
  iapply HRange $$ %r %rq %o %log [Hm]
  · iunfold rangePre
    iframe Hm Hr
    ipureintro; exact Hk
  inext
  iintro %resp %trace %err Hpost
  iapply HΦ
  iunfold rangePost at Hpost
  icases Hpost with ⟨%oc, %Hst, HR⟩
  iexists oc
  iframe HR
  ipureintro
  exact chainStep_alarm_range ns cr rq log oc Hk.2.1 Hst

/-- **A transaction through the uber-applier's chain**: the outcome `alarmTxn` (the txn
package's `txnModel`: `checkTxn`'s error or the server's run `srvRunTxn`), its answer, the log it
commits. -/
theorem chain_txn (E : AEnv GF) (ns cr : Bool) (a : GoInterface) :
    applierSpec E (alarmChain ns cr) a ⊢
      ∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
      □ (∀ (r : Loc) (skip : Bool) (rq : IRRModel) (t : TxnModel) (log : mvcc.Log)
          (Pre Q Post : IProp GF),
        {{ txnPre E (alarmChain ns cr) (.ok ai) r rq t log Pre Q Post }}
          (App (App (Val #(methods ai.ty go!"Txn" ai.v)) (Val #r)) (Val #skip))
        {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
            ∃ oc : Outcome, ⌜alarmTxn ns cr t log oc⌝ ∗ txnOutcomeIs log t skip resp err oc ∗
              kvOwn E (oc.logAfter log) ∗ chainRes (alarmChain ns cr) (.ok ai) ∗ (Post ∨ Pre) }}) := by
  iintro #Hs
  iunfold applierSpec at Hs
  icases Hs with ⟨%ai, %Ha, #Ht⟩
  iexists ai
  isplitr
  · ipureintro; exact Ha
  iunfold applierTriples at Ht
  icases Ht with ⟨-, -, -, #HTxn, -⟩
  imodintro
  iintro %r %skip %rq %t %log %Pre %Q %Post
  imodintro
  iintro %Φ Hpre HΦ
  iunfold txnPre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hm⟩
  iapply HTxn $$ %r %skip %rq %t %log %Pre %Q %Post [Hm]
  · iunfold txnPre
    iframe Hm Hr
    ipureintro; exact Hk
  inext
  iintro %resp %trace %err Hpost
  iapply HΦ
  iunfold kvPost at Hpost
  icases Hpost with ⟨%oc, %Hst, HR⟩
  iexists oc
  iframe HR
  ipureintro
  exact chainStep_alarm_txn ns cr rq t log oc Hk.2.1 Hk.1 Hst

end triples

#print axioms Perennial.EtcdGrove.apply.chain_put
#print axioms Perennial.EtcdGrove.apply.chain_deleteRange
#print axioms Perennial.EtcdGrove.apply.chain_range
#print axioms Perennial.EtcdGrove.apply.chain_txn
#print axioms Perennial.EtcdGrove.apply.wp_newApplierV3Backend
#print axioms Perennial.EtcdGrove.apply.wp_newQuotaApplierV3
#print axioms Perennial.EtcdGrove.apply.wp_newApplierV3Capped
#print axioms Perennial.EtcdGrove.apply.wp_newApplierV3Corrupt
#print axioms Perennial.EtcdGrove.apply.wp_newAuthApplierV3

/-! ## Unit 2: the uber-applier and `Apply` (`uber_applier.go`, `apply.go`)

Every function of the two files has a `Spec`/`Proof` pair and a linked result: `NewUberApplier`
(`uberIs`, and the chain the alarms ask for, `alarmChain ns cr`), `newApplierV3` (`baseChain`),
`restoreAlarms`, `uberApplier.Apply`, `dispatch`, `uberApplier.Alarm`, `noSideEffect` and
`apply.Apply` (`wp_Apply : apply.Apply.spec`): the server's contract (one critical section of the
batch lock after the hook, or none; nothing without `v3`) with the KV: the apply thread's
`applyKV E ua x` goes to `x'` by `applyStep rq v3 x x' out` (`InvUber.lean`). What that relation
says, at the chains the uber-applier builds:

* **A KV entry** (`apply_kv`): skipped (a range no one waits for) or rejected by the admin check,
  the state as it is; or dispatched, its outcome the chain's (`alarmPut`, `alarmDelete`,
  `alarmRange`, `alarmTxn`: the txn package's `putModel`, `deleteModel`, `txnModel`, or a
  rejection), the log the outcome commits, the chain as it was.
* **A read** (`apply_readonly_no_write`): a range, or a read-only transaction, leaves the log.
* **A rejection** (`apply_rejected_no_write`): rejected by the admin check or by a layer
  (corrupt, capped, auth, the backend's checks), the log as it is.
* **Without `v3`** (`apply_no_v3_no_write`): the state as it is (a replayed entry).
-/

/-- A chain whose backend leaves the log leaves it (the quota's `ErrNoSpace` reports after the
backend's write, it does not write). -/
theorem chainStep_log_same (B : IRRModel → mvcc.Log → Outcome → Prop) (rq : IRRModel)
    (log : mvcc.Log) (hB : ∀ o, B rq log o → o.logAfter log = log) :
    ∀ (c : Chain) (o : Outcome), chainStep B c rq log o → o.logAfter log = log := by
  intro c
  induction c with
  | backend => intro o h; exact hB o h
  | auth c ih =>
    intro o h
    simp only [chainStep] at h
    split at h
    · rcases h with rfl | h
      · rfl
      · exact ih o h
    · exact ih o h
  | quota c ih =>
    intro o h
    simp only [chainStep] at h
    split at h
    · obtain ⟨o', h', hq⟩ := h
      rcases hq with rfl | ⟨log', rfl, rfl⟩
      · exact ih _ h'
      · simpa [Outcome.logAfter] using ih _ h'
    · exact ih o h
  | capped c ih =>
    intro o h
    simp only [chainStep] at h
    split at h
    · subst h; rfl
    · split at h
      · rcases h with rfl | h
        · rfl
        · exact ih o h
      · exact ih o h
  | corrupt c ih =>
    intro o h
    simp only [chainStep] at h
    split at h
    · subst h; rfl
    · exact ih o h

theorem ite_eq_iff' {α : Sort _} {c : Prop} [Decidable c] {a b k : α} :
    (if c then a else b) = k ↔ (c ∧ a = k) ∨ (¬c ∧ b = k) := by
  by_cases h : c <;> simp [h]

theorem dispatchKind_put (rq : IRRModel) (h : dispatchKind rq = .put) : rq.put.isSome = true := by
  simp only [dispatchKind, ite_eq_iff', reduceCtorEq, and_false, false_or, or_false] at h
  exact h.2.2.2.2.2.1

theorem dispatchKind_deleteRange (rq : IRRModel) (h : dispatchKind rq = .deleteRange) :
    rq.deleteRange.isSome = true := by
  simp only [dispatchKind, ite_eq_iff', reduceCtorEq, and_false, false_or, or_false] at h
  exact h.2.2.2.2.2.2.1

theorem dispatchKind_txn (rq : IRRModel) (h : dispatchKind rq = .txn) : rq.txn.isSome = true := by
  simp only [dispatchKind, ite_eq_iff', reduceCtorEq, and_false, false_or, or_false] at h
  exact h.2.2.2.2.2.2.2.1

/-- **A KV entry through `apply.Apply`** (with `v3`, the uber-applier at `alarmChain ns cr`):
skipped or rejected by the admin check (the state as it is), or dispatched: the outcome of the
chain in the txn package's terms, the log it commits, the chain as it was. -/
theorem apply_kv (rq : IRRModel) (x x' : ApplyKV) (out : ApplyOut) (ns cr : Bool)
    (hc : x.chain = alarmChain ns cr) (hk : isKVKind (dispatchKind rq) = true)
    (h : applyStep rq true x x' out) :
    ((out = .skipped ∨ out = .rejected) ∧ x' = x) ∨
    ∃ o sk, out = .dispatched o sk ∧ x'.log = o.logAfter x.log ∧ x'.chain = x.chain ∧
      ((∃ op, rq.put = some op ∧ dispatchKind rq = .put ∧ alarmPut ns cr op x.log o) ∨
       (∃ op, rq.deleteRange = some op ∧ dispatchKind rq = .deleteRange ∧
          alarmDelete cr op x.log o) ∨
       (dispatchKind rq = .range ∧ alarmRange cr x.log o) ∨
       (∃ t, rq.txn = some t ∧ dispatchKind rq = .txn ∧ alarmTxn ns cr t x.log o)) := by
  cases out with
  | skipped => exact Or.inl ⟨Or.inl rfl, h.2⟩
  | rejected => exact Or.inl ⟨Or.inr rfl, h.2⟩
  | dispatched o sk =>
    obtain ⟨-, hd, hl, hch⟩ := h
    have hpre : preV3Kind (dispatchKind rq) = false := by
      revert hk; cases dispatchKind rq <;> simp [isKVKind, preV3Kind]
    have hst : storeKind (dispatchKind rq) = true := by
      revert hk; cases dispatchKind rq <;> simp [isKVKind, storeKind]
    have hcs : chainStep backendStep x.chain rq x.log o := by
      simpa [dispatchStep, hpre, hst] using hd
    have hch' : x'.chain = x.chain := by
      rcases hch with h | ⟨-, hal, -⟩
      · exact h
      · rw [hal] at hk; simp [isKVKind] at hk
    rw [hc] at hcs
    refine Or.inr ⟨o, sk, rfl, hl, hch', ?_⟩
    cases hdk : dispatchKind rq <;> rw [hdk] at hk <;> simp [isKVKind] at hk
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, chainStep_alarm_range ns cr rq x.log o hdk hcs⟩))
    · obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp (dispatchKind_put rq hdk)
      exact Or.inl ⟨op, hop, rfl, chainStep_alarm_put ns cr rq op x.log o hdk hop hcs⟩
    · obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp (dispatchKind_deleteRange rq hdk)
      exact Or.inr (Or.inl ⟨op, hop, rfl, chainStep_alarm_delete ns cr rq op x.log o hdk hop hcs⟩)
    · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (dispatchKind_txn rq hdk)
      exact Or.inr (Or.inr (Or.inr ⟨t, ht, rfl, chainStep_alarm_txn ns cr rq t x.log o hdk ht hcs⟩))

/-- **A read writes nothing**: a range, or a read-only transaction, through `apply.Apply` leaves
the log. -/
theorem apply_readonly_no_write (rq : IRRModel) (v3 : Bool) (x x' : ApplyKV) (out : ApplyOut)
    (hk : dispatchKind rq = .range ∨
      (dispatchKind rq = .txn ∧ ∃ t, rq.txn = some t ∧ txn.txnReadonly t = true))
    (h : applyStep rq v3 x x' out) : x'.log = x.log := by
  cases out with
  | skipped => rw [h.2]
  | rejected => rw [h.2]
  | dispatched o sk =>
    obtain ⟨-, hd, hl, -⟩ := h
    rw [hl]
    have hB : ∀ o', backendStep rq x.log o' → o'.logAfter x.log = x.log := by
      intro o' hb
      unfold backendStep at hb
      rcases hk with hk | ⟨hk, t, ht, hro⟩
      · rw [hk] at hb; subst hb; rfl
      · rw [hk] at hb
        obtain ⟨t', ht', hb⟩ := hb
        rw [ht] at ht'; cases ht'
        rcases hb with rfl | ⟨rfl, hnil⟩
        · rfl
        · simp only [Outcome.logAfter, mvcc.commitLog]; rw [if_pos (hnil hro)]
    unfold dispatchStep at hd
    split at hd
    · subst hd; rfl
    · split at hd
      · exact chainStep_log_same backendStep rq x.log hB x.chain o hd
      · exact hd

/-- **A rejection writes nothing**: rejected by the admin check, or dispatched to a rejection
(a layer's or the backend's checks), the log as it is. -/
theorem apply_rejected_no_write (rq : IRRModel) (v3 : Bool) (x x' : ApplyKV) (out : ApplyOut)
    (hr : out = .rejected ∨ ∃ k sk, out = .dispatched (.rejected k) sk)
    (h : applyStep rq v3 x x' out) : x'.log = x.log := by
  rcases hr with rfl | ⟨k, sk, rfl⟩
  · rw [h.2]
  · rw [h.2.2.1]; rfl

/-- **Without `v3`, nothing changes** (a replayed entry): the KV's log and the chain as they were. -/
theorem apply_no_v3_no_write (rq : IRRModel) (x x' : ApplyKV) (out : ApplyOut)
    (h : applyStep rq false x x' out) : x' = x := by
  cases out with
  | skipped => exact h.2
  | rejected => exact h.2
  | dispatched o sk =>
    obtain ⟨-, hd, hl, hch⟩ := h
    have ho : o = .applied x.log false := by
      unfold dispatchStep at hd; simpa using hd
    have hc : x'.chain = x.chain := by
      rcases hch with h | ⟨h, -⟩
      · exact h
      · cases h
    cases x; cases x'
    simp_all [Outcome.logAfter]

#print axioms Perennial.EtcdGrove.apply.wp_Apply
#print axioms Perennial.EtcdGrove.apply.wp_NewUberApplier
#print axioms Perennial.EtcdGrove.apply.uberApplier.wp_dispatch
#print axioms Perennial.EtcdGrove.apply.apply_kv
#print axioms Perennial.EtcdGrove.apply.apply_readonly_no_write
#print axioms Perennial.EtcdGrove.apply.apply_rejected_no_write
#print axioms Perennial.EtcdGrove.apply.apply_no_v3_no_write

/-! ## Unit 0: the trust boundary and the callees linked elsewhere -/

#print axioms Perennial.EtcdGrove.apply.pbutil.wp_MustUnmarshalMessage
#print axioms Perennial.EtcdGrove.apply.semver.wp_MustParse
#print axioms Perennial.EtcdGrove.mvcc.store.wp_Rev
#print axioms Perennial.EtcdGrove.txn.wp_Txn

end apply
end EtcdGrove
end Perennial
