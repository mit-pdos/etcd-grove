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
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Results

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
(`apply.apply_kv`). The writing `Txn` and the read side are unit 3's. -/

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

#print axioms Perennial.EtcdGrove.applyEntries_model
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
#print axioms Perennial.EtcdGrove.wait_new
#print axioms Perennial.EtcdGrove.idutil_next

end EtcdGrove
end Perennial
