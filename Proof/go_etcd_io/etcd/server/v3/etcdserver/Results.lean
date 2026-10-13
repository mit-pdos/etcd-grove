/-
The results of the server's apply thread (`server/v3/etcdserver`, the consistent index and the
apply loop), restated at top level, with the trust base of each printed in the build log
(`#print axioms`). Lean-first (no Rocq counterpart).

**The end-to-end result** (the apply package's unit 3, 2026-10-12): the apply thread's
`applyEntries` keeps the consistent-index protocol (`loopOk`: no entry's writes applied twice,
none above `ci` skipped; `InvApply.lean`) and, through the proved `apply.Apply`, takes the KV
from `x` to `x'` by `entriesStep c (unapplied ai ms) x x'` (`applyEntries_model`): the batch's
entries above the applied index, in order, each normal entry above the consistent index `c`
applied by the txn package's client model, each at or below it replayed without effect. Its
premises: the protocol's (`loopOk`, `entriesFrom`), the KV's (`entriesOk`: every normal entry's
data decode to a request with an id or a header, neither a compaction nor empty, satisfying the
txn package's premises at the state it meets), and the components' contracts (the apply
package's `Contracts.lean`, `applyConfChange`'s, the names-only callees').

The corollaries are on the run's trace (`entriesStep_trace`: the states it passes through):
* **A KV entry above `ci`** (`applyEntries_kv`): skipped or rejected by the admin check (the
  state as it is), or dispatched to the outcome of the uber-applier's chain (`alarmPut`,
  `alarmDelete`, `alarmRange`, `alarmTxn` of the apply package's `Results.lean`: the txn
  package's `putModel`, `deleteModel`, `txnModel`, the range, or a layer's rejection), the log
  the outcome commits (`apply.apply_kv`).
* **A replayed entry** (`applyEntries_replay_no_write`): an entry at or below `ci` changes
  nothing (the double-apply half of the consistent-index guarantee, on the KV).
* **A rejected entry** (`applyEntries_rejected_no_write`): rejected by the admin check or by a
  layer, the log as it is.

**The apply loop's step and the applied index** (the request path's unit 4b, 2026-10-13):
`applyAll_model` (linked `applyAll`: `applyEntries_model`'s content for the whole step, the
applied index's waiters triggered at the new applied index, under raft's no-snapshot contract);
`applied_log_at` (each `setAppliedIndex` deposits the KV log after its entry as the log applied
through that index, `appliedLogAt`, which agrees); with `range_linearizable`, a linearizable read
at the committed index `c` returns the state of a log extending the one applied through some
index `ci₀ ≥ c`, and that log is exactly the apply thread's after the entry `ci₀`. The read
loop's contracts are met by the server's objects: `read_server` (`isReadServer` for `*EtcdServer`)
and `read_raft` (`isReadRaft` for its `raftNode`); `wait_time` (`pkg/wait`'s `*timeList` is a
`WaitTime`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadRaft
public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeListIfc
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Results

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ## One entry -/

/-- The chain stays one the uber-applier builds (`alarmChain`) across an entry. -/
theorem batchStep_alarmChain (c : w64) (m : EntryModel) (y y' : apply.ApplyKV) (ns cr : Bool)
    (h : batchStep c m y y') (hc : y.chain = apply.alarmChain ns cr) :
    ∃ ns' cr', y'.chain = apply.alarmChain ns' cr' := by
  unfold batchStep at h
  split at h
  · obtain ⟨out, h⟩ := h
    unfold entryStep at h
    split at h
    · rw [h.1]; exact ⟨ns, cr, hc⟩
    · obtain ⟨rq, -, -, -, h⟩ := h
      cases out with
      | skipped => rw [h.2]; exact ⟨ns, cr, hc⟩
      | rejected => rw [h.2]; exact ⟨ns, cr, hc⟩
      | dispatched o sk =>
        rcases h.2.2.2 with h' | ⟨-, -, ns', cr', h'⟩
        · rw [h', hc]; exact ⟨ns, cr, rfl⟩
        · exact ⟨ns', cr', h'⟩
  · rw [h]; exact ⟨ns, cr, hc⟩

/-- **A KV entry above `ci`** (`v3`): skipped (no data, or no waiter and no side effect) or
rejected by the admin check, the state as it is; or dispatched, its outcome the chain's in the
txn package's terms (`apply.apply_kv`). -/
theorem entryStep_kv (m : EntryModel) (y y' : apply.ApplyKV) (out : apply.ApplyOut)
    (rq : apply.IRRModel) (ns cr : Bool) (h : entryStep m true y y' out)
    (hd : apply.irrDecode m.data = some rq) (hk : apply.isKVKind (apply.dispatchKind rq) = true)
    (hc : y.chain = apply.alarmChain ns cr) :
    ((out = .skipped ∨ out = .rejected) ∧ y' = y) ∨
    ∃ o sk, out = .dispatched o sk ∧ y'.log = o.logAfter y.log ∧ y'.chain = y.chain ∧
      ((∃ op, rq.put = some op ∧ apply.dispatchKind rq = .put ∧
          apply.alarmPut ns cr op y.log o) ∨
       (∃ op, rq.deleteRange = some op ∧ apply.dispatchKind rq = .deleteRange ∧
          apply.alarmDelete cr op y.log o) ∨
       (apply.dispatchKind rq = .range ∧ apply.alarmRange cr y.log o) ∨
       (∃ t, rq.txn = some t ∧ apply.dispatchKind rq = .txn ∧
          apply.alarmTxn ns cr t y.log o)) := by
  unfold entryStep at h
  split at h
  · exact Or.inl ⟨Or.inl h.2, h.1⟩
  · obtain ⟨rq', -, hd', -, h⟩ := h
    rw [hd] at hd'; cases hd'
    exact apply.apply_kv rq y y' out ns cr hc hk h

/-- **A replayed entry changes nothing** (`v3 = false`). -/
theorem entryStep_no_v3 (m : EntryModel) (y y' : apply.ApplyKV) (out : apply.ApplyOut)
    (h : entryStep m false y y' out) : y' = y := by
  unfold entryStep at h
  split at h
  · exact h.1
  · obtain ⟨rq, -, -, -, h⟩ := h
    exact apply.apply_no_v3_no_write rq y y' out h

/-- **A rejected entry writes nothing**: rejected by the admin check, or dispatched to a layer's
or the backend's rejection. -/
theorem entryStep_rejected_no_write (m : EntryModel) (v3 : Bool) (y y' : apply.ApplyKV)
    (out : apply.ApplyOut) (h : entryStep m v3 y y' out)
    (hr : out = .rejected ∨ ∃ k sk, out = .dispatched (.rejected k) sk) : y'.log = y.log := by
  unfold entryStep at h
  split at h
  · rw [h.1]
  · obtain ⟨rq, -, -, -, h⟩ := h
    exact apply.apply_rejected_no_write rq v3 y y' out hr h

/-! ## The apply loop -/

section triples
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The apply loop implements the client model over the committed entries** (`s.applyEntries
(ep, ap)`, linked): the consistent-index protocol kept (`loopOk`, `ep.appliedi` advanced to the
last entry), and the apply thread's KV taken from `x` to `x'` by `entriesStep c (unapplied ai ms)`
(`c` the consistent index at the start), under `entriesOk`. -/
theorem applyEntries_model : EtcdServer.applyEntries.spec (GF := GF) (hG := hG) :=
  EtcdServer.wp_applyEntries

/-- **The apply loop's step** (`s.applyAll(ep, ap)`, linked; the request path's unit 4b):
`applyEntries_model`'s content for the whole step (the KV from `x` to `x'` by `entriesStep`
over the entries above the applied index, `loopOk` kept), the applied index at the new `ai'`
(`srvAppliedOwn`, `appliedAtLeast`) with the log applied through it the KV's (`appliedLogAt γr ai'
x'.log`), the applied index's waiters through `ai'` released (`applyWait.Trigger`), under raft's
no-snapshot contract (`ap.snapshot = nil`) and the snapshot, compaction and merged-snapshot
contracts. -/
theorem applyAll_model : EtcdServer.applyAll.spec (GF := GF) (hG := hG) :=
  EtcdServer.wp_applyAll

/-- **The applied logs** (the apply-side half of `range_linearizable`'s log; the request path's
unit 4b): `setAppliedIndex` (linked), right after the entry at index `v'` with mvcc's certificate
of the KV log `L`, deposits `L` as the log applied through `v'` (`appliedLogAt γr v' L`); `apply`
(linked) does it for every entry, so its result's index has the KV's log after the batch; and the
log applied through an index is unique. Together with `range_linearizable`: a linearizable read at
the committed index `c` returns the state of a log extending the one applied through some index
`ci₀ ≥ c`, and that log is exactly the apply thread's after the entry at `ci₀`. -/
theorem applied_log_at :
    EtcdServer.setAppliedIndex.spec (GF := GF) (hG := hG) ∧
    EtcdServer.apply.spec (GF := GF) (hG := hG) ∧
    ∀ (γr : ReadNames) (i : w64) (L L' : mvcc.Log),
      ⊢ appliedLogAt (GF := GF) γr i L -∗ appliedLogAt γr i L' -∗ ⌜L = L'⌝ :=
  ⟨EtcdServer.wp_setAppliedIndex, EtcdServer.wp_apply, appliedLogAt_agree⟩

/-- **`*EtcdServer` meets the read loop's `server` contract** (`isReadServer`, the request path's
unit 4b; its nine methods linked): from the server's facts (`isServerReq`, `isServerRead`), with
the caller's resource `srvReadLR s` (the logger's and the two notifiers' reader slots) and the id
resource `idCred ρ.ids 1` (the id budget). -/
theorem read_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      isReadServer (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) γr (srvReadLR s)
        (idCred ρ.ids 1) :=
  isReadServer_of_server EtcdServer.wp_ApplyWait EtcdServer.wp_Done EtcdServer.wp_Stopping
    EtcdServer.wp_LeaderChanged EtcdServer.wp_FirstCommitInTermNotify EtcdServer.wp_NextRequestID
    EtcdServer.wp_RequestTimeout EtcdServer.wp_AppliedIndex EtcdServer.wp_Logger s E ρ γr

/-- **The server's raft wrapper meets the read loop's `raftInterface` contract** (`isReadRaft`, the
request path's unit 4b; `ReadState` and `ReadIndex` linked): over the node contract
(`isRaftNodeIfc`, raft's trust boundary: `ReadIndex` registers at a committed bound, the `Ready`'s
read states answer the registrations), at the read names `E.γr` and registrations `E.RQ`. -/
theorem read_raft (E : RNEnv GF) (γ : RNNames) (r : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ⊢
      isReadRaft (interface.mkOk (go.GoType.PointerType raftNode.ty) #r) E.γr E.RQ :=
  isReadRaft_of_raftNode raftNode.wp_ReadState raftNode.wp_ReadIndex E γ r

/-- **`pkg/wait`'s `*timeList` is a `WaitTime`** (`isWaitTime`, the request path's unit 4b;
`Wait`, `Trigger` linked): for a predicate `P` of deadlines monotone downward (`NewTimeList`'s
premise, with `P 0` and `closec` closed). -/
theorem wait_time (tl : Loc) (P : w64 → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ isTimeList tl P ⊢
      isWaitTime (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.timeList.ty)
        #tl) P :=
  isWaitTime_of_timeList wait.timeList.wp_Wait wait.timeList.wp_Trigger tl P

end triples

/-- **The batch, entry by entry** (`entriesStep_trace` on the batch `applyEntries` applies): the
states `xs` the KV passes through, `xs[n]` before the `n`-th entry. -/
theorem applyEntries_trace (c ai : w64) (ms : List EntryModel) (x x' : apply.ApplyKV)
    (h : entriesStep c (unapplied ai ms) x x') :
    ∃ xs : List apply.ApplyKV, xs.length = (unapplied ai ms).length + 1 ∧ xs[0]? = some x ∧
      xs[(unapplied ai ms).length]? = some x' ∧
      ∀ (n : Nat) (m : EntryModel) (y y' : apply.ApplyKV), (unapplied ai ms)[n]? = some m →
        xs[n]? = some y → xs[n + 1]? = some y' → batchStep c m y y' :=
  entriesStep_trace c _ x x' h

/-- **Every KV entry above `ci` is applied by the client model**: in a run of a batch from a KV
whose chain is one the uber-applier builds, each normal entry above `c` whose request is a KV
request is skipped or rejected by the admin check (the state as it is), or dispatched to the
outcome of the chain at the state it meets (`alarmPut`/`alarmDelete`/`alarmRange`/`alarmTxn`:
the txn package's `putModel`/`deleteModel`/the range/`txnModel`, or a layer's rejection), which
commits the log `o.logAfter`. -/
theorem applyEntries_kv (c : w64) (ms : List EntryModel) (x x' : apply.ApplyKV) (ns0 cr0 : Bool)
    (h : entriesStep c ms x x') (hc0 : x.chain = apply.alarmChain ns0 cr0) :
    ∃ xs : List apply.ApplyKV, xs.length = ms.length + 1 ∧ xs[0]? = some x ∧
      xs[ms.length]? = some x' ∧
      ∀ (n : Nat) (m : EntryModel) (y y' : apply.ApplyKV) (rq : apply.IRRModel),
        ms[n]? = some m → xs[n]? = some y → xs[n + 1]? = some y' →
        m.typ = W32 0 → uint.Z c < uint.Z m.index → apply.irrDecode m.data = some rq →
        apply.isKVKind (apply.dispatchKind rq) = true →
        ∃ (ns cr : Bool) (out : apply.ApplyOut), y.chain = apply.alarmChain ns cr ∧
          (((out = .skipped ∨ out = .rejected) ∧ y' = y) ∨
          ∃ o sk, out = .dispatched o sk ∧ y'.log = o.logAfter y.log ∧ y'.chain = y.chain ∧
            ((∃ op, rq.put = some op ∧ apply.dispatchKind rq = .put ∧
                apply.alarmPut ns cr op y.log o) ∨
             (∃ op, rq.deleteRange = some op ∧ apply.dispatchKind rq = .deleteRange ∧
                apply.alarmDelete cr op y.log o) ∨
             (apply.dispatchKind rq = .range ∧ apply.alarmRange cr y.log o) ∨
             (∃ t, rq.txn = some t ∧ apply.dispatchKind rq = .txn ∧
                apply.alarmTxn ns cr t y.log o))) := by
  induction ms generalizing x ns0 cr0 with
  | nil =>
    simp only [entriesStep] at h; subst h
    exact ⟨[x'], rfl, rfl, rfl, by simp⟩
  | cons m0 ms ih =>
    obtain ⟨x1, h1, hr⟩ := h
    obtain ⟨ns1, cr1, hc1⟩ := batchStep_alarmChain c m0 x x1 ns0 cr0 h1 hc0
    obtain ⟨xs, hl, h0, hL, hs⟩ := ih x1 ns1 cr1 hr hc1
    refine ⟨x :: xs, by simp [hl], rfl, by simpa using hL, ?_⟩
    intro n m y y' rq hm hy hy' ht hgt hd hk
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm hy
      simp only [Nat.zero_add, List.getElem?_cons_succ, h0, Option.some.injEq] at hy'
      subst hm hy hy'
      unfold batchStep at h1
      rw [ite_eq_left ht] at h1
      obtain ⟨out, h1⟩ := h1
      rw [decide_eq_true hgt] at h1
      exact ⟨ns0, cr0, out, hc0, entryStep_kv _ _ _ out rq ns0 cr0 h1 hd hk hc0⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hm hy hy'
      exact hs n m y y' rq hm hy hy' ht hgt hd hk

/-- **The replayed entries write nothing** (the double-apply half of the consistent-index
guarantee, on the KV): every step of a batch at an entry at or below `ci` leaves the KV as it
is; so a batch at or below `ci` leaves it. -/
theorem applyEntries_replay_no_write (c : w64) (m : EntryModel) (y y' : apply.ApplyKV)
    (h : batchStep c m y y') (hle : uint.Z m.index ≤ uint.Z c) : y' = y := by
  unfold batchStep at h
  split at h
  · obtain ⟨out, h⟩ := h
    rw [decide_eq_false (by omega)] at h
    exact entryStep_no_v3 m y y' out h
  · exact h

theorem applyEntries_replay_all (c : w64) (ms : List EntryModel) (x x' : apply.ApplyKV)
    (h : entriesStep c ms x x') (hle : ∀ m ∈ ms, uint.Z m.index ≤ uint.Z c) : x' = x := by
  induction ms generalizing x with
  | nil => exact h
  | cons m ms ih =>
    obtain ⟨x1, h1, hr⟩ := h
    have e1 := applyEntries_replay_no_write c m x x1 h1 (hle m (by simp))
    rw [e1] at hr
    exact ih x hr (fun m' hm' => hle m' (by simp [hm']))

/-- **A rejected entry writes nothing**: a step of a batch at a normal entry whose outcome is a
rejection (the admin check's, or a layer's or the backend's in `dispatch`) leaves the log. -/
theorem applyEntries_rejected_no_write (c : w64) (m : EntryModel) (y y' : apply.ApplyKV)
    (out : apply.ApplyOut) (h : entryStep m (decide (uint.Z c < uint.Z m.index)) y y' out)
    (hr : out = .rejected ∨ ∃ k sk, out = .dispatched (.rejected k) sk) : y'.log = y.log :=
  entryStep_rejected_no_write m _ y y' out h hr

/-! ## The request path (`v3_server.go`, `pkg/wait`, `pkg/idutil`; unit 2 of the request path)

**The handoff** (`processInternalRaftRequestOnce`, linked): a request proposed through raft with a
fresh id (`idutil.Generator.Next`), registered in the wait (`pkg/wait`) with the expectation that
its result be the apply thread's result of applying it (`resultΨ`), returns that result: the
apply package's `applyStep` and `applyResultIs` of the request the proposed data decode to, at
the KV state the entry met, with mvcc's certificate of the log after (`resultIs`); or an error,
with the proposal, if made, deposited with raft (it may still be applied: etcd's documented
behavior on a timeout). Its premises: the raft contract (`raftPropose`), the server's request-path
fields and invariants (`isServerReq`), a reader slot of `s.leadTimeMu`, one id credit, and, on the
apply side, the entries' claims (`entryWaitOk`, from raft's `batchCommitted`, unit 4).

**`put_applied`, `deleteRange_applied`** (linked `EtcdServer.Put`, `DeleteRange`): a `(resp, nil)`
return is the apply package's answer to the request (`putOutcomeIs`/`deleteOutcomeIs` at the log
`x.log` the entry met, no error), dispatched at `x` to `x'`, with `idxCert` of `x'.log`; an error
is the apply's (`appliedErr`) or the proposal's (`srvMaybeDeposited`: `put_err` is the right
disjunct of the same postcondition). `put_applied_model`/`deleteRange_applied_model`: through the
uber-applier's chain (`alarmChain`), the outcome is `alarmPut`/`alarmDelete` (the txn package's
`putModel`/`deleteModel`, or a layer's rejection) and the log after is the outcome's
(`apply.apply_kv`). The writing `Txn` and the read side: unit 3b's, below. -/

section request
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The handoff** (see the section header). -/
theorem request_handoff : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG) :=
  EtcdServer.wp_processInternalRaftRequestOnce

/-- **`put_applied` and `put_err`** (see the section header). -/
theorem put_applied : EtcdServer.Put.spec (GF := GF) (hG := hG) :=
  EtcdServer.wp_Put

/-- **`deleteRange_applied`** (see the section header). -/
theorem deleteRange_applied : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG) :=
  EtcdServer.wp_DeleteRange

/-- **The wait registry** (`pkg/wait`'s `New`, linked). -/
theorem wait_new : wait.New.spec (GF := GF) (hG := hG) :=
  wait.wp_New

/-- **The id generator** (`pkg/idutil`, linked). -/
theorem idutil_next : idutil.Generator.Next.spec (GF := GF) (hG := hG) :=
  idutil.Generator.wp_Next

end request

/-- **What a successful `Put` applied** (pure; the success components of `put_applied`): through
the uber-applier's chain `alarmChain ns cr`, the put's outcome is `alarmPut` (the txn package's
`putModel`, or a layer's rejection) and the log after is the outcome's. -/
theorem put_applied_model (op : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
    (o : apply.Outcome) (skip ns cr : Bool) (hc : x.chain = apply.alarmChain ns cr)
    (h : apply.applyStep (apply.withHeader (irrPut op) hm) true x x' (.dispatched o skip)) :
    x'.log = o.logAfter x.log ∧ apply.alarmPut ns cr op x.log o := by
  have hk : apply.dispatchKind (apply.withHeader (irrPut op) hm) = .put := by
    simp [apply.dispatchKind, apply.withHeader, irrPut, apply.irrEmpty]
  rcases apply.apply_kv _ x x' _ ns cr hc (by rw [hk]; rfl) h with ⟨hout, -⟩ | ⟨o', sk, hout, hlog, -, hcases⟩
  · rcases hout with h1 | h1 <;> cases h1
  · cases hout
    refine ⟨hlog, ?_⟩
    rcases hcases with ⟨op', hop, -, ha⟩ | ⟨-, -, hd, -⟩ | ⟨hd, -⟩ | ⟨-, -, hd, -⟩
    · simp [apply.withHeader, irrPut] at hop
      subst hop; exact ha
    all_goals (rw [hk] at hd; cases hd)

/-- **What a successful `DeleteRange` applied** (pure): through `alarmChain ns cr`, the delete's
outcome is `alarmDelete` of the decoded request's delete `op'` (`deleteModel`, or a layer's
rejection), the log after the outcome's. -/
theorem deleteRange_applied_model (op op' : OpFull) (hm : apply.HeaderModel) (rq' : apply.IRRModel)
    (x x' : apply.ApplyKV) (o : apply.Outcome) (skip ns cr : Bool)
    (hc : x.chain = apply.alarmChain ns cr)
    (hw : irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq')
    (hop : rq'.deleteRange = some op')
    (h : apply.applyStep rq' true x x' (.dispatched o skip)) :
    x'.log = o.logAfter x.log ∧ apply.alarmDelete cr op' x.log o := by
  have hk : apply.dispatchKind rq' = .deleteRange := by
    rw [hw.2.2.1]; simp [apply.dispatchKind, apply.withHeader, irrDeleteRange, apply.irrEmpty]
  rcases apply.apply_kv _ x x' _ ns cr hc (by rw [hk]; rfl) h with ⟨hout, -⟩ | ⟨o', sk, hout, hlog, -, hcases⟩
  · rcases hout with h1 | h1 <;> cases h1
  · cases hout
    refine ⟨hlog, ?_⟩
    rcases hcases with ⟨-, -, hd, -⟩ | ⟨op'', hop', -, ha⟩ | ⟨hd, -⟩ | ⟨-, -, hd, -⟩
    · rw [hk] at hd; cases hd
    · rw [hop] at hop'; cases hop'; exact ha
    all_goals (rw [hk] at hd; cases hd)

/-! ## The read side and `Txn` (unit 3b of the request path)

**`range_serializable`**, **`range_linearizable`** (linked `EtcdServer.Range`, restated): a
`(resp, nil)` of `Range` is the txn package's answer at a certified log of at least `NewStore`'s
two revisions, the response header's id fields owned (for the gRPC layer to fill); serializable,
in the client model's terms (`txn.rangeResultClient`: `rangeKvsOk` of `rangeSel` of the state
read, for a sort not cut early); linearizable, read after the read index (`readIndexOk γr c`:
the applied index reached an index at least the committed index `c` the caller knew of, the read
loop's contract `isRead`) and, since the request path's unit 4b, of a log extending the log the
apply thread had applied through some index `ci₀ ≥ c` (`appliedLogAt γr ci₀ L₀`, `L₀ <+: log`; see
`applied_log_at`). An error is one the
gRPC layer can take (`applyErrIs`: the read loop's, the auth store's, `ErrFutureRev`, the
context's).

**`txn_readonly`** (linked `EtcdServer.Txn` at a read-only request): the server's run of the
transaction at a certified log (`txnReadOk`, both serializability modes: after the read index
unless every get is serializable), the id credit back. **`txn_applied`** (at a writing request):
the apply thread's application of the request the proposed data decode to (`txnAppliedOk`),
possibly with header-only ranges (`SkipRangeExecution`: the wait's `IsRegistered` is "some
boolean" in its contract, so the model admits the run of a transaction whose waiter had timed
out, the plan's suspect 2, here for a waiter that did not), or the apply's or the proposal's
error. **`txn_applied_model`** (pure): through the uber-applier's chain the outcome is `alarmTxn`
(the txn package's `txnModel` or a layer's rejection), the log after the outcome's. -/

section read
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open go_etcd_io.etcd.api.v3

/-- **`range_linearizable`** (see the section header). -/
theorem range_linearizable (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull)
    (hlin : o.base.serializable = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
        txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
            ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ ∗ readIndexOk γr c ∗
            (∃ (ci₀ : w64) (L₀ : mvcc.Log), ⌜uint.Z c ≤ uint.Z ci₀⌝ ∗ appliedLogAt γr ci₀ L₀ ∗
              ⌜L₀ <+: log⌝) ∗
            txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true ∗
            txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp)) ∨
         (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }} := by
  iintro %Φ Hpre HΦ
  iapply (EtcdServer.wp_Range s E ρ γr c ctx cd r o) $$ [Hpre]
  · iexact Hpre
  inext
  iintro %resp %err ⟨Hrc, H⟩
  iapply HΦ
  iframe Hrc
  icases H with (⟨%Hok, H⟩ | H)
  · ileft
    iunfold rangeReadOk at H
    simp only [hlin, Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨%log, #Hc, %Hl, #Hrl, #Hres, Hown⟩
    iunfold readLogOk at Hrl
    icases Hrl with ⟨#Hri, #Hlog⟩
    isplitr
    · ipureintro; exact Hok
    iexists log
    iframe Hc Hri Hlog Hres Hown
    ipureintro; exact Hl
  · iright; iexact H

/-- **`range_serializable`** (see the section header): in the client model's terms, for a
request whose sort is not cut early (a serializable one's whole answer: it takes no read index;
a linearizable one's adds `range_linearizable`'s `readIndexOk`). -/
theorem range_serializable (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull)
    (hcut : ¬ txn.cutEarly o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
        txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
            ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ ∗
            txn.rangeResultClient resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true ∗
            txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp)) ∨
         (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }} := by
  iintro %Φ ⟨#Hp, #Hq, #Hd, Hrc, #Hctx, #Hr, %Hv⟩ HΦ
  ihave %Hset := txn.rangeRequestIs_sortSet r o $$ Hr
  iapply (EtcdServer.wp_Range s E ρ γr c ctx cd r o) $$ [Hrc]
  · iframe #; iframe Hrc; ipureintro; exact Hv
  inext
  iintro %resp %err ⟨Hrc, H⟩
  iapply HΦ
  iframe Hrc
  icases H with (⟨%Hok, H⟩ | H)
  · ileft
    iunfold rangeReadOk at H
    icases H with ⟨%log, #Hcert, %Hlen, -, #Hres, Hown⟩
    isplitr
    · ipureintro; exact Hok
    iexists log
    iframe Hcert Hown
    isplitr
    · ipureintro; exact Hlen
    iapply txn.rangeResult_client _ _ _ _ o true Hset hcut $$ Hres
  · iright; iexact H

/-- **`txn_readonly`** (see the section header). -/
theorem txn_readonly (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel)
    (hro : txn.txnReadonly t = true) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗
        srvRdCall s E γr c ∗ context.isContext ctx cd ∗ txn.txnRequestIs r t ∗
        ⌜txn.txnGetsOk t⌝ }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        srvLeadTimeReader s ∗ srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnReadOk E γr c t resp) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }} := by
  iintro %Φ ⟨#Hp, #Hq, #Hd, Hlt, Hcr, Hrc, #Hctx, #Hr, %Hg⟩ HΦ
  have hT := EtcdServer.wp_Txn s E ρ γr c ctx cd r t
  simp only [hro, ↓reduceIte] at hT
  iapply hT $$ [Hlt Hcr Hrc]
  · iframe #; iframe Hlt Hcr Hrc; ipureintro; exact fun _ => Hg
  inext
  iintro %resp %err ⟨Hlt, Hrc, Hcr, H⟩
  iapply HΦ
  iframe Hlt Hrc Hcr H

/-- **`txn_applied`** (see the section header). -/
theorem txn_applied (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel)
    (hw : txn.txnReadonly t = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗
        srvRdCall s E γr c ∗ context.isContext ctx cd ∗ txn.txnRequestIs r t }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        srvLeadTimeReader s ∗ srvRdCall s E γr c ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnAppliedOk E t resp) ∨
         (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ txnErrOk E ρ t err)) }} := by
  iintro %Φ ⟨#Hp, #Hq, #Hd, Hlt, Hcr, Hrc, #Hctx, #Hr⟩ HΦ
  have hT := EtcdServer.wp_Txn s E ρ γr c ctx cd r t
  simp only [hw, Bool.false_eq_true, ↓reduceIte] at hT
  iapply hT $$ [Hlt Hcr Hrc]
  · iframe #; iframe Hlt Hcr Hrc; ipureintro; exact fun h => h.elim
  inext
  iintro %resp %err ⟨Hlt, Hrc, H⟩
  iapply HΦ
  iframe Hlt Hrc H

end read

/-- **What a successful writing `Txn` applied** (pure; the success components of `txn_applied`):
through the uber-applier's chain `alarmChain ns cr`, the transaction `t'` of the decoded request
has the outcome `alarmTxn` (the txn package's `txnModel`, or a layer's rejection), the log after
the outcome's. -/
theorem txn_applied_model (t t' : TxnModel) (hm : apply.HeaderModel) (rq' : apply.IRRModel)
    (x x' : apply.ApplyKV) (o : apply.Outcome) (skip ns cr : Bool)
    (hc : x.chain = apply.alarmChain ns cr)
    (hw : irrWireOf (apply.withHeader (irrTxn t) hm) rq')
    (ht : rq'.txn = some t')
    (h : apply.applyStep rq' true x x' (.dispatched o skip)) :
    x'.log = o.logAfter x.log ∧ apply.alarmTxn ns cr t' x.log o := by
  have hk : apply.dispatchKind rq' = .txn := by
    rw [hw.2.2.1]; simp [apply.dispatchKind, apply.withHeader, irrTxn, apply.irrEmpty]
  rcases apply.apply_kv _ x x' _ ns cr hc (by rw [hk]; rfl) h with ⟨hout, -⟩ | ⟨o', sk, hout, hlog, -, hcases⟩
  · rcases hout with h1 | h1 <;> cases h1
  · cases hout
    refine ⟨hlog, ?_⟩
    rcases hcases with ⟨-, -, hd, -⟩ | ⟨-, -, hd, -⟩ | ⟨hd, -⟩ | ⟨t'', ht', -, ha⟩
    · rw [hk] at hd; cases hd
    · rw [hk] at hd; cases hd
    · rw [hk] at hd; cases hd
    · rw [ht] at ht'; cases ht'; exact ha

/-! ## The apply thread's KV over the real backend (2026-10-13, unit 6)

The server's results above are generic in the store's backend instance (`txn.isKV` no longer
pins `γ.kb = none`). `NewStore` over the real backend (`mvcc_NewStore_backend`, resting on the
backend's proof and bbolt's key-value contract) makes what the apply thread starts with: the
store as the txn package's `isKV`, its reader slots, the sole writer of the initial log, and a
supply of `N` write tokens (`txn.storeWTs`, the backend's write-back tokens: `applyEntries`
spends one per entry). The premises are the backend creator's (the backend's constructor is not
proved): the backend made for the real instance, its post-lock hook set for good, **`keySized`**
(fewer than `2 ^ 62` entries of the `Key` bucket in any state a read transaction holds: a
genuine assumption, nothing in etcd bounds a bucket's size), the clients' view of the empty
`Key` bucket, the lock resource's registration right, `N + 2` write-back tokens (`NewStore`
spends two) and a reader token per reader slot; and, since the merge with the store's compaction
(unit 5a, 2026-10-13), `NewStore`'s premise on its configuration (`0 ≤ CompactionBatchLimit`).
The store is never compacted here: `NewStore`'s compaction right is given up
(`compactRight_freeze`), so its readers are those of a never-compacted store (`storeReader`). -/

section backend
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The apply thread's KV over the real backend**: `NewStore` on a fresh backend of the real
instance `d` gives a store `s` of that instance (`γ.kb = some d`) that is the txn package's
`isKV`, with its reader slots, the sole writer of `NewStore`'s log `[[], []]` and `N` write
tokens: with the store's lessor's leases (none in the empty state), the apply thread's
`apply.kvOwn` and `applyEntries`' write budget, for a server whose environment is the store's. -/
theorem server_kv_backend (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF)
    (f : GoFunc) (hf : f ≠ func.nil) (N : Nat) (hcfg : 0 ≤ sint.Z cfg.CompactionBatchLimit') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.lateReg d.gx ∗
        ownToks d.γB.wb (N + 2) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        mvcc.isLessor le γl }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d⌝ ∗
        txn.isKV (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.store.ty) #s) s γ ∗ mvcc.hookIs γ Pk #f ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.storeReader s γ) ∗
        txn.soleWriter γ [[], []] ∗ txn.storeWTs γ N ∗ mvcc.storeCloser s }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hhk, #Hsz, Hv, Hrg, Hw, Hrts, #Hle⟩ HΦ
  rw [show N + 2 = (N + 1) + 1 by omega]
  icases ownToks_add_1 1 (N + 1) d.γB.wb $$ Hw with ⟨Hw, Hw1⟩
  icases ownToks_add_1 1 N d.γB.wb $$ Hw with ⟨Hw, Hw2⟩
  iapply wp_fupd
  wp_apply (mvcc_NewStore_backend lg le cfg d hP γb γl Pk f hf hcfg) $$ [Hv Hrg Hw1 Hw2 Hrts]
    as %s ⟨%γ, %Hγ, #Hst, #Hhk', -, Hrds, Htoks, #Hc, Hcl, -, Hright⟩
  · iframe #; iframe Hv Hrg Hrts
    unfold backend.wbTok
    iframe Hw1 Hw2
  -- the apply thread's store is never compacted (the compaction is not in the server's model):
  -- the compaction right given up, the readers those of a never-compacted store (as the
  -- watchable store's `newWatchableStore` does)
  imod mvcc.compactRight_freeze γ ⊤ $$ Hright with #Hfrz
  ihave Hrds := mvcc.storeReaders_of s γ _ $$ [$Hfrz $Hrds]
  imodintro
  iapply HΦ
  iexists γ
  isplitr
  · ipureintro; exact Hγ
  iframe Hhk' Hrds Hcl
  isplitr
  · iunfold txn.isKV; iframe Hst; ipureintro; rfl
  isplitl [Htoks]
  · iapply txn.soleWriter_of_NewStore γ; iframe Htoks Hc
  unfold txn.storeWTs
  rw [Hγ.2.2]
  iexact Hw

end backend

#print axioms Perennial.EtcdGrove.server_kv_backend
#print axioms Perennial.EtcdGrove.applyEntries_model
#print axioms Perennial.EtcdGrove.applyAll_model
#print axioms Perennial.EtcdGrove.applied_log_at
#print axioms Perennial.EtcdGrove.read_server
#print axioms Perennial.EtcdGrove.read_raft
#print axioms Perennial.EtcdGrove.wait_time
#print axioms Perennial.EtcdGrove.applyEntries_trace
#print axioms Perennial.EtcdGrove.applyEntries_kv
#print axioms Perennial.EtcdGrove.applyEntries_replay_no_write
#print axioms Perennial.EtcdGrove.applyEntries_replay_all
#print axioms Perennial.EtcdGrove.applyEntries_rejected_no_write
#print axioms Perennial.EtcdGrove.EtcdServer.wp_apply
#print axioms Perennial.EtcdGrove.EtcdServer.wp_applyEntryNormal
#print axioms Perennial.EtcdGrove.request_handoff
#print axioms Perennial.EtcdGrove.put_applied
#print axioms Perennial.EtcdGrove.deleteRange_applied
#print axioms Perennial.EtcdGrove.put_applied_model
#print axioms Perennial.EtcdGrove.deleteRange_applied_model
#print axioms Perennial.EtcdGrove.range_linearizable
#print axioms Perennial.EtcdGrove.range_serializable
#print axioms Perennial.EtcdGrove.txn_readonly
#print axioms Perennial.EtcdGrove.txn_applied
#print axioms Perennial.EtcdGrove.txn_applied_model
#print axioms Perennial.EtcdGrove.wait_new
#print axioms Perennial.EtcdGrove.idutil_next

end EtcdGrove
end Perennial
