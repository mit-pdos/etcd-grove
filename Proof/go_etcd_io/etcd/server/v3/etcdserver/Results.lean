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
premises: the protocol's (`loopOk`, `entriesFrom`), the KV's (`logShape`: every normal entry's
data decode to a request with an id or a header, neither a compaction nor empty, satisfying the
txn package's premises at every state where the size clauses hold, which they do at the state it
meets, the apply thread's log being small by the store's time receipts: D19c's move), and the components' contracts (the apply
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
`applied_log_at` (each `setAppliedIndex` publishes the KV log after its entry as the log applied
through that index, `appliedLogAt`, which agrees; since unit C2a, 2026-10-14, the log is deposited
ahead, `applied_predeposit`, before the entry's result reaches its proposer, and the applied logs
grow with the index, `appliedMono`); with `range_linearizable`, a linearizable read
at the committed index `c` returns the state of a log extending the one applied through some
index `ci₀ ≥ c`, and that log is exactly the apply thread's after the entry `ci₀`. The read
loop's contracts are met by the server's objects: `read_server` (`isReadServer` for `*EtcdServer`)
and `read_raft` (`isReadRaft` for its `raftNode`); `wait_time` (`pkg/wait`'s `*timeList` is a
`WaitTime`).

**The server's raft contracts, from raft's specs** (stage R7b of the raft v3.7 retarget,
2026-10-16; D10): `node_contract_ifc` (`isRaftNodeIfc`: `Ready`, `Advance`, `Tick`, `ReadIndex`
from raft's linked `node.wp_*`; `Stop` the premise `rnStopOk`), `node_contract_propose`
(`raftPropose` from `node.wp_Propose`) and `node_contract_memstor` (`isRNMemStor` from raft's
`memStorage_Append`), over the wrapper's names (`rnEnvOk`, raft's `isNode`, the commit invariant
and the committed index's); the errors are raft's (`NodeBridge.lean`; the two error facts
`rnCtxErrOk`, a done context's, and `rnPropErrOk`, a proposal's own result, were premises until
stage R7c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.TokenKeeperRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthSteps
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthFuel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AdminChain
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadRaft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeBridge
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeStart
public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeListIfc
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CindexBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.HooksBackend
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorContract
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildLemmas
public import Proof.go_etcd_io.etcd.server.v3.auth.NewAuthStoreOn
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.auth.Latest
public import Proof.go_etcd_io.etcd.server.v3.auth.ReadLb
public import Proof.go_etcd_io.etcd.server.v3.auth.FreshCheck
public import Proof.go_etcd_io.etcd.server.v3.auth.FreshWrap
public import Proof.go_etcd_io.etcd.server.v3.auth.authStore__UserAdd_sure
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestAdmin
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatestTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnKVL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVOutcomeOn
public import Proof.go_etcd_io.etcd.server.v3.auth.authStore__UserAdd_tieSure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AdminChain
public import Proof.go_uber_org.zap.Int
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAllocOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StartOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyTieOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdminL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyEntryOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDeadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDeadAdminOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.UberOn

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
theorem batchStep_alarmChain (on : Bool) (c : w64) (m : EntryModel) (y y' : apply.ApplyKV) (ns cr : Bool)
    (h : batchStep c m y y') (hc : y.chain = apply.alarmChain on ns cr) :
    ∃ ns' cr', y'.chain = apply.alarmChain on ns' cr' := by
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
        · rw [hc, apply.alarmChain_authOn] at h'; exact ⟨ns', cr', h'⟩
  · rw [h]; exact ⟨ns, cr, hc⟩

/-- **A KV entry above `ci`** (`v3`): skipped (no data, or no waiter and no side effect) or
rejected by the admin check, the state as it is; or dispatched, its outcome the chain's in the
txn package's terms (`apply.apply_kv`). -/
theorem entryStep_kv (m : EntryModel) (y y' : apply.ApplyKV) (out : apply.ApplyOut)
    (rq : apply.IRRModel) (on ns cr : Bool) (h : entryStep m true y y' out)
    (hd : apply.irrDecode m.data = some rq) (hk : apply.isKVKind (apply.dispatchKind rq) = true)
    (hc : y.chain = apply.alarmChain on ns cr) :
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
    exact apply.apply_kv rq y y' out on ns cr hc hk h

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
(`c` the consistent index at the start), under the entries' shapes (`logShape`). -/
theorem applyEntries_model : EtcdServer.applyEntries.spec (GF := GF) (hG := hG) :=
  EtcdServer.wp_applyEntries

/-- **The apply loop's step** (`s.applyAll(ep, ap)`, linked; the request path's unit 4b):
`applyEntries_model`'s content for the whole step (the KV from `x` to `x'` by `entriesStep`
over the entries above the applied index, `loopOk` kept), the applied index at the new `ai'`
(`srvAppliedOwn`, `appliedAtLeast`) with the log applied through it the KV's (`appliedLogAt γr ai'
x'.log`), the applied index's waiters through `ai'` released (`applyWait.Trigger`), under raft's
no-snapshot contract (`ap.snapshot = nil`) and the snapshot, compaction and merged-snapshot
contracts. (2026-10-26) Under `ErrorStringLeaf`: the compaction (`compactRaftLog`, proved since)
decides `errors.Is(err, raft.ErrCompacted)` of an `errors.New` error. -/
theorem applyAll_model [ErrorStringLeaf] : EtcdServer.applyAll.spec (GF := GF) (hG := hG) :=
  EtcdServer.wp_applyAll

/-- **The applied logs** (the apply-side half of `range_linearizable`'s log; the request path's
unit 4b): `setAppliedIndex` (linked), right after the entry at index `v'` with mvcc's certificate
of the KV log `L`, publishes `L` as the log applied through `v'` (`appliedLogAt γr v' L`; deposited
ahead since unit C2a, 2026-10-14, `srvAppliedPre`, `applied_predeposit`); `apply`
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
resource `idCred ρ.ids 1` (the id budget; since R7b the id's `NextRequestID` also mints raft's
fresh read-context token and read credit from the server's mint, at the read names `ρ.rd = γr`). -/
theorem read_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (hρ : ρ.rd = γr) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      isReadServer (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) γr (srvReadLR s)
        (idCred ρ.ids 1) :=
  isReadServer_of_server EtcdServer.wp_ApplyWait EtcdServer.wp_Done EtcdServer.wp_Stopping
    EtcdServer.wp_LeaderChanged EtcdServer.wp_FirstCommitInTermNotify EtcdServer.wp_NextRequestID
    EtcdServer.wp_RequestTimeout EtcdServer.wp_AppliedIndex EtcdServer.wp_Logger s E ρ γr hρ

/-- **The server's raft wrapper meets the read loop's `raftInterface` contract** (`isReadRaft`, the
request path's unit 4b; `ReadState` and `ReadIndex` linked): over the node contract
(`isRaftNodeIfc`, discharged from raft's node specs since stage R7b, `node_contract_ifc`:
`ReadIndex` registers at a committed bound, the `Ready`'s read states answer the registrations),
at the read names `E.γr` and registrations `E.RQ`. -/
theorem read_raft (E : RNEnv GF) (γ : RNNames) (r : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ⊢
      isReadRaft (interface.mkOk (go.GoType.PointerType raftNode.ty) #r) E.γr E.RQ :=
  isReadRaft_of_raftNode raftNode.wp_ReadState raftNode.wp_ReadIndex E γ r

/-- **The node meets the server's `raft.Node` contract** (`isRaftNodeIfc`; stage R7b, D10): `Ready`,
`Advance`, `Tick` and `ReadIndex` from raft's linked `node.wp_Ready`, `wp_Advance`, `wp_Tick`,
`wp_ReadIndex` (`isRaftNodeIfc_of_isNode`), over the wrapper's facts of `E` (`rnEnvOk`), raft's
`isNode` by the wrapper's names (`rnIsNode`), the server's view of raft's commit invariant
(`srvRaftLogInv`) and the committed index's invariant (`srvCommittedInv`, the log `ReadIndex`'s
bound is read from); `Stop` is the premise `rnStopOk` (raft's model never stops). The context's
error is one the gRPC layer takes since stage R7c (raft's `ctxErr` names it, by the trust-boundary
spec `context.ErrDone`; until then the premise `rnCtxErrOk`). -/
theorem node_contract_ifc (E : RNEnv GF) (γ : RNNames) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnIsNode γ ∗ srvRaftLogInv E.γr.raft ∗ srvCommittedInv s E.γr ∗
      rnStopOk γ.nl ∗ rnMemStorReg γ ⊢
      isRaftNodeIfc E γ (rnNodeIface γ) :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  isRaftNodeIfc_of_isNode E γ s node.wp_Ready
    node.wp_Advance node.wp_Tick
    node.wp_ReadIndex node.wp_ApplyConfChange

/-- **The node meets the request path's `raftPropose`** (stage R7b, D10): from raft's linked
`node.wp_Propose` and, since audit phase B3 (2026-10-18), `node.wp_ApplyConfChange`
(`raftPropose_of_isNode`), over `rnEnvOk`, `rnIsNode` and `srvRaftLogInv`. The
errors are raft's since stage R7c (`propErr`: `nil`, `ErrStopped`, the context's `Canceled` or
`DeadlineExceeded`, the proposal's `ErrProposalDropped`), each one the gRPC layer takes
(`applyErrIs_of_propErr`, by the server's and the read package's facts). -/
theorem node_contract_propose (E : RNEnv GF) (γ : RNNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnIsNode γ ∗ srvRaftLogInv E.γr.raft ⊢
      raftPropose E.γr.raft (rnNodeIface γ) :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  raftPropose_of_isNode E γ node.wp_Propose node.wp_ApplyConfChange

/-- **The `MemoryStorage` meets the wrapper's `isRNMemStor`** (stage R7b, D10): raft's
`memStorage_Append` (over the linked `MemoryStorage.wp_Append`), for a registered storage. -/
theorem node_contract_memstor (γ : RNNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rnMemStorReg γ ⊢
      isRNMemStor γ γ.ms :=
  isRNMemStor_of_memstorage γ

/-- **The server's raft wrapper from raft's `StartNode`** (stage R8b-C of the raft v3.7 retarget,
2026-10-16; D12, `NodeStart.lean`): on the new cluster's path, `bootstrappedRaft.newRaftNode`
(linked: through it raft's `wp_StartNode`, `Bootstrap`'s conf-change entries at term 1, and
`newRaftNode`) yields the wrapper's struct value with its components, the loop's and the apply
side's tokens at `[]`, `srvRaftLogInv` at `pre = []`, and the installer of `isRaftNode` at the
address `NewServer` copies the struct to, from the new cluster's ghost allocation
(`ownRaftGhost_alloc_boot`: a stub, `sorryAx` below, until stage R8b-A lands), the budget, a fresh
registered `MemoryStorage`, the server's own invariants and the trust-boundary premises
(`NodeStart.lean`'s header classifies them). `PreVote` and `CheckQuorum` either way (etcd's
default configuration) since 2026-10-17. -/
theorem server_raft_node_start (reg : GName) : NodeStartSpec (GF := GF) reg :=
  letI : MemStorReg GF := ⟨reg⟩
  raftNode_of_StartNode reg bootstrappedRaft.wp_newRaftNode node.wp_Ready node.wp_Advance
    node.wp_Tick node.wp_ReadIndex node.wp_Step node.wp_ReportUnreachable node.wp_ReportSnapshot
    node.wp_Propose node.wp_ApplyConfChange

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
theorem applyEntries_kv (c : w64) (ms : List EntryModel) (x x' : apply.ApplyKV) (on ns0 cr0 : Bool)
    (h : entriesStep c ms x x') (hc0 : x.chain = apply.alarmChain on ns0 cr0) :
    ∃ xs : List apply.ApplyKV, xs.length = ms.length + 1 ∧ xs[0]? = some x ∧
      xs[ms.length]? = some x' ∧
      ∀ (n : Nat) (m : EntryModel) (y y' : apply.ApplyKV) (rq : apply.IRRModel),
        ms[n]? = some m → xs[n]? = some y → xs[n + 1]? = some y' →
        m.typ = W32 0 → uint.Z c < uint.Z m.index → apply.irrDecode m.data = some rq →
        apply.isKVKind (apply.dispatchKind rq) = true →
        ∃ (ns cr : Bool) (out : apply.ApplyOut), y.chain = apply.alarmChain on ns cr ∧
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
    obtain ⟨ns1, cr1, hc1⟩ := batchStep_alarmChain on c m0 x x1 ns0 cr0 h1 hc0
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
      exact ⟨ns0, cr0, out, hc0, entryStep_kv _ _ _ out rq on ns0 cr0 h1 hd hk hc0⟩
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

/-- **`request_delivered`** (the request path's unit 4d; linked `applyEntryNormal` at a known
registration): the apply thread, applying the normal entry `m` whose data decode to the request
`rq` with id `id`, where `id` was registered with the consumer token `t` (`waitRegd`, what the
proposer's `Register` returned), applies it in full (`out.waived = false`: neither skipped as
side-effect-free nor its ranges skipped, `SkipRangeExecution`) unless that registration is gone
(`waitGone`: a `Trigger(id, _)` took it out of the registry before the apply thread's
`IsRegistered`, the proposer's own `Trigger(id, nil)` on giving up, or a `Trigger` with a result
from an earlier application of the same id). With `request_handoff`: a proposer still waiting
(its consumer token unspent) receives the result of its entry's full application, unless its
context ended first. Since 2026-10-14 (unit C2a), with the apply thread's applied-index resources
at `v = m.index - 1` (`srvAppliedOwn`, the log `appliedLogAt γr v x.log`) and the entry committed
(`committedAtLeast γr m.index`): the KV log after the entry is deposited ahead as the log applied
through `m.index` (`srvAppliedPre`), the witness the result carries. (D22 S8d, 2026-10-26: with
`v3`, the state loaded, `stLoaded γ st = st`, as `apply`'s `ConsistentIndex` leaves it:
`applyEntryNormal`'s premise, `notes/decisions.md`.) -/
theorem request_delivered (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (b : GoInterface) (e : Loc) (m : EntryModel)
    (st : ApplyState) (v3 : Bool) (x : apply.ApplyKV) (γr : ReadNames) (rq : apply.IRRModel)
    (id : w64) (t : GName) (v : w64) (A : List EntryModel) (hne : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hid : apply.irrId rq = some id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServer s γ ci TM E ρ γr ∗ entryWaitOk ρ E m ∗ waitRegd ρ.wait id t ∗ entryAt e m ∗
        applyThread γ st ∗ applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗
        srvApplyKV s E ρ.wait x ∗ mvcc.storeWT E.γ ∗ srvFS s ∗
        srvAppliedOwn γr v ∗ appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
        kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗ srvRLogLb γr.raft (A ++ [m]) ∗
        ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)⌝ ∗
        ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
        ⌜st.pending = false ∧ entryOk x m ∧ m.typ = W32 0⌝ ∗
        (if v3 then iprop(ciApplying ci m.index m.term ∗
            ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
              uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝)
         else iprop(True)) }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
        (Val #e)) (Val #v3))
    {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvFS s ∗
        (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
          ⌜entryStep m v3 x x' out⌝ ∗ (⌜out.waived = false⌝ ∨ waitGone ρ.wait id t) ∗
          srvAppliedPre γr v m.index x'.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x' ∗
          srvRest E γr (A ++ [m])) ∗
        (if v3 then iprop(ciApplying ci m.index m.term ∗
            ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩)
         else applyThread γ st) }} := by
  iintro %Φ ⟨#Hpkg, #Hsrv, #Hewo, #Hreg, #He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, Hfs, Hao, #HLv, #Hcm, Hka,
    HRS, #HAm, %HkA, %Hvi, %Hpo, Hv3⟩ HΦ
  iapply (EtcdServer.wp_applyEntryNormal s γ ci TM E ρ b e m st v3 x γr (some t) v A)
    $$ [Hst Hbe Hlr Hgr HKV Hwt Hfs Hv3 Hao Hka HRS]
  · iframe Hst Hbe Hlr Hgr HKV Hwt Hfs Hv3 Hao Hka HRS
    iframe #
    isplitr
    · iunfold entryRegd
      imodintro
      iintro %rq' %id' %h
      have : rq' = rq := by rw [hdec] at h; exact (Option.some.inj h.1).symm
      subst this
      have : id' = id := by rw [hid] at h; exact (Option.some.inj h.2).symm
      subst this
      iunfold waitRegdOpt
      iframe Hreg
      ipureintro; intro h; cases h
    ipureintro; exact ⟨HkA, Hvi, Hpo⟩
  inext
  iintro ⟨Hbe, Hlr, Hgr, Hfs, ⟨%x', %out, HKV, %Hstep, #Hdel, Hpre, Hka, HRS⟩, Hpost⟩
  iapply HΦ
  iframe Hbe Hlr Hgr Hfs Hpost
  iexists x', out
  iframe HKV Hpre Hka HRS
  isplitr
  · ipureintro; exact Hstep
  iunfold entryDelivered at Hdel
  icases Hdel with (%Hw | ⟨%rq', %id', %h, #Hg⟩)
  · ileft; ipureintro
    rcases Hw with h | h
    · exact absurd h hne
    · exact h
  · iright
    have : rq' = rq := by rw [hdec] at h; exact (Option.some.inj h.1).symm
    subst this
    have : id' = id := by rw [hid] at h; exact (Option.some.inj h.2).symm
    subst this
    iunfold waitGoneOpt at Hg
    iexact Hg

/-- **The wait registry** (`pkg/wait`'s `New`, linked). -/
theorem wait_new : wait.New.spec (GF := GF) (hG := hG) :=
  wait.wp_New

/-- **The id generator** (`pkg/idutil`, linked). -/
theorem idutil_next : idutil.Generator.Next.spec (GF := GF) (hG := hG) :=
  idutil.Generator.wp_Next

end request

/-- **What a successful `Put` applied** (pure; the success components of `put_applied`): through
the uber-applier's chain `alarmChain on ns cr`, the put's outcome is `alarmPut` (the txn package's
`putModel`, or a layer's rejection) and the log after is the outcome's. -/
theorem put_applied_model (op : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
    (o : apply.Outcome) (skip on ns cr : Bool) (hc : x.chain = apply.alarmChain on ns cr)
    (h : apply.applyStep (apply.withHeader (irrPut op) hm) true x x' (.dispatched o skip)) :
    x'.log = o.logAfter x.log ∧ apply.alarmPut ns cr op x.log o := by
  have hk : apply.dispatchKind (apply.withHeader (irrPut op) hm) = .put := by
    simp [apply.dispatchKind, apply.withHeader, irrPut, apply.irrEmpty]
  rcases apply.apply_kv _ x x' _ on ns cr hc (by rw [hk]; rfl) h with ⟨hout, -⟩ | ⟨o', sk, hout, hlog, -, hcases⟩
  · rcases hout with h1 | h1 <;> cases h1
  · cases hout
    refine ⟨hlog, ?_⟩
    rcases hcases with ⟨op', hop, -, ha⟩ | ⟨-, -, hd, -⟩ | ⟨hd, -⟩ | ⟨-, -, hd, -⟩
    · simp [apply.withHeader, irrPut] at hop
      subst hop; exact ha
    all_goals (rw [hk] at hd; cases hd)

/-- **What a successful `DeleteRange` applied** (pure): through `alarmChain on ns cr`, the delete's
outcome is `alarmDelete` of the decoded request's delete `op'` (`deleteModel`, or a layer's
rejection), the log after the outcome's. -/
theorem deleteRange_applied_model (op op' : OpFull) (hm : apply.HeaderModel) (rq' : apply.IRRModel)
    (x x' : apply.ApplyKV) (o : apply.Outcome) (skip on ns cr : Bool)
    (hc : x.chain = apply.alarmChain on ns cr)
    (hw : irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq')
    (hop : rq'.deleteRange = some op')
    (h : apply.applyStep rq' true x x' (.dispatched o skip)) :
    x'.log = o.logAfter x.log ∧ apply.alarmDelete cr op' x.log o := by
  have hk : apply.dispatchKind rq' = .deleteRange := by
    rw [hw.2.2.1]; simp [apply.dispatchKind, apply.withHeader, irrDeleteRange, apply.irrEmpty]
  rcases apply.apply_kv _ x x' _ on ns cr hc (by rw [hk]; rfl) h with ⟨hout, -⟩ | ⟨o', sk, hout, hlog, -, hcases⟩
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
loop's contract `isReadNotify`) and, since the request path's unit 4b, of a log extending the log the
apply thread had applied through some index `ci₀ ≥ c` (`appliedLogAt γr ci₀ L₀`, `L₀ <+: log`; see
`applied_log_at`). An error is one the
gRPC layer can take (`applyErrIs`: the read loop's, the auth store's, `ErrFutureRev`, the
context's).

**`txn_readonly`** (linked `EtcdServer.Txn` at a read-only request): the server's run of the
transaction at a certified log (`txnReadOk`, both serializability modes: after the read index
unless every get is serializable), the id credit back. **`txn_applied`** (at a writing request,
with its client's update over the whole state, `txnPermit`; 2026-10-15, unit T2): the apply
thread's application of the request the proposed data decode to (`txnAppliedOk`, with `□ Q` of the
state the update linearized at: unit W-M3, the state of the log the transaction met),
possibly with header-only ranges (`SkipRangeExecution`: the apply loops call the wait's
`IsRegistered` knowing nothing of the id's registration, so the model admits the run of a
transaction whose waiter had timed out, the plan's suspect 2, here for a waiter that did not;
`request_delivered` excludes it at a known registration, unless that registration is gone), or
the apply's or the proposal's
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
    (ot : Option Loc) (te : Bool) (F : mvcc.Log)
    (hlin : o.base.serializable = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
        traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
        mvcc.idxCert E.γ.idx F }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
            ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ F <+: log⌝ ∗ readIndexOk γr c ∗
            (∃ (ci₀ : w64) (L₀ : mvcc.Log), ⌜uint.Z c ≤ uint.Z ci₀⌝ ∗ appliedLogAt γr ci₀ L₀ ∗
              ⌜L₀ <+: log⌝) ∗
            txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true ∗
            txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp)) ∨
         (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }} := by
  iintro %Φ ⟨#Hp, #Hq, #Hd, Hrc, #Hctx, Hct, Hot, #Hr, %Hv, #HF⟩ HΦ
  iapply (EtcdServer.wp_Range s E ρ γr c ctx cd r o ot te (fun _ => iprop(True)) F) $$ [Hrc Hct Hot]
  · iframe #; iframe Hrc Hct Hot
    isplitr
    · ipureintro; exact Hv
    iunfold kvDep; iright; ipureintro; rfl
  inext
  iintro %resp %err ⟨Hrc, H⟩
  iapply HΦ
  iframe Hrc
  icases H with (⟨%Hok, -, H⟩ | H)
  · ileft
    iunfold rangeReadOk at H
    simp only [hlin, Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨%log, #Hc, -, %Hl, #Hrl, -, #Hres, Hown⟩
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
    (ot : Option Loc) (te : Bool) (F : mvcc.Log)
    (hcut : ¬ txn.cutEarly o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
        traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
        mvcc.idxCert E.γ.idx F }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
            ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ ∗
            txn.rangeResultClient resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true ∗
            txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp)) ∨
         (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }} := by
  iintro %Φ ⟨#Hp, #Hq, #Hd, Hrc, #Hctx, Hct, Hot, #Hr, %Hv, #HF⟩ HΦ
  ihave %Hset := txn.rangeRequestIs_sortSet r o $$ Hr
  iapply (EtcdServer.wp_Range s E ρ γr c ctx cd r o ot te (fun _ => iprop(True)) F) $$ [Hrc Hct Hot]
  · iframe #; iframe Hrc Hct Hot
    isplitr
    · ipureintro; exact Hv
    iunfold kvDep; iright; ipureintro; rfl
  inext
  iintro %resp %err ⟨Hrc, H⟩
  iapply HΦ
  iframe Hrc
  icases H with (⟨%Hok, -, H⟩ | H)
  · ileft
    iunfold rangeReadOk at H
    icases H with ⟨%log, #Hcert, -, %Hlen, -, -, #Hres, Hown⟩
    isplitr
    · ipureintro; exact Hok
    iexists log
    iframe Hcert Hown
    isplitr
    · ipureintro; exact ⟨Hlen.1, Hlen.2.1⟩
    iapply txn.rangeResult_client _ _ _ _ o true Hset hcut $$ Hres
  · iright; iexact H

/-- **`txn_readonly`** (see the section header). -/
theorem txn_readonly (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel)
    (ot : Option Loc) (te : Bool) (F : mvcc.Log)
    (hro : txn.txnReadonly t = true) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗
        srvRdCall s E γr c ∗ context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
        traceutil.ownTraceOpt ot te ∗ txn.txnRequestIs r t ∗
        ⌜txn.txnGetsOk t⌝ ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        srvLeadTimeReader s ∗ srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnReadOk E γr c F t (fun _ => iprop(True)) resp) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }} := by
  iintro %Φ ⟨#Hp, #Hq, #Hd, Hlt, Hcr, Hrc, #Hctx, Hct, Hot, #Hr, %Hg, #HF⟩ HΦ
  have hT := EtcdServer.wp_Txn s E ρ γr c ctx cd r t (fun _ => iprop(True)) (fun _ => iprop(True))
    ot te F
  simp only [hro, ↓reduceIte] at hT
  iapply hT $$ [Hlt Hcr Hrc Hct Hot]
  · iframe #; iframe Hlt Hcr Hrc Hct Hot
    isplitr
    · ipureintro; exact fun _ => Hg
    iunfold kvDep; iright; ipureintro; rfl
  inext
  iintro %resp %err ⟨Hlt, Hrc, Hcr, H⟩
  iapply HΦ
  iframe Hlt Hrc Hcr H

/-- **`txn_applied`** (see the section header). -/
theorem txn_applied (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel)
    (Q : KVState → IProp GF) (ot : Option Loc) (te : Bool) (F : mvcc.Log)
    (hw : txn.txnReadonly t = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗
        srvRdCall s E γr c ∗ context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
        traceutil.ownTraceOpt ot te ∗ txn.txnRequestIs r t ∗ mvcc.idxCert E.γ.idx F ∗
        txnPermit ρ.kv t Q }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        srvLeadTimeReader s ∗ srvRdCall s E γr c ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnAppliedOk E ρ.rd F t Q resp) ∨
         (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ txnErrOk E ρ F t err)) }} := by
  iintro %Φ ⟨#Hp, #Hq, #Hd, Hlt, Hcr, Hrc, #Hctx, Hct, Hot, #Hr, #HF, Hnp⟩ HΦ
  have hT := EtcdServer.wp_Txn s E ρ γr c ctx cd r t Q (fun _ => iprop(True)) ot te F
  simp only [hw, Bool.false_eq_true, ↓reduceIte] at hT
  iapply hT $$ [Hlt Hcr Hrc Hct Hot Hnp]
  · iframe #; iframe Hlt Hcr Hrc Hct Hot Hnp; ipureintro; exact fun h => h.elim
  inext
  iintro %resp %err ⟨Hlt, Hrc, H⟩
  iapply HΦ
  iframe Hlt Hrc H

end read

/-- **What a successful writing `Txn` applied** (pure; the success components of `txn_applied`):
through the uber-applier's chain `alarmChain on ns cr`, the transaction `t'` of the decoded request
has the outcome `alarmTxn` (the txn package's `txnModel`, or a layer's rejection), the log after
the outcome's. -/
theorem txn_applied_model (tw : txn.TxnModelW) (t' : TxnModel) (hm : apply.HeaderModel) (rq' : apply.IRRModel)
    (x x' : apply.ApplyKV) (o : apply.Outcome) (skip on ns cr : Bool)
    (hc : x.chain = apply.alarmChain on ns cr)
    (hw : irrWireOf (apply.withHeader (irrTxn tw) hm) rq')
    (ht : rq'.txn = some t')
    (h : apply.applyStep rq' true x x' (.dispatched o skip)) :
    x'.log = o.logAfter x.log ∧ apply.alarmTxn ns cr t' x.log o := by
  have hk : apply.dispatchKind rq' = .txn := by
    rw [hw.2.2.1]; simp [apply.dispatchKind, apply.withHeader, irrTxn, apply.irrEmpty]
  rcases apply.apply_kv _ x x' _ on ns cr hc (by rw [hk]; rfl) h with ⟨hout, -⟩ | ⟨o', sk, hout, hlog, -, hcases⟩
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
The store is never compacted here: `NewStore`'s half of the compaction revision's authority is
given up (`crevFrozen_alloc`), so its readers are those of a never-compacted store
(`storeReader`); the backend records no compaction (`bkNoCmp`, `NewStore`'s: D19l (v) (A), D22 S-g),
and the right to close the store holds its scheduler's stop token (D19m (C)). -/

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
    (f : GoFunc) (hf : f ≠ func.nil) (rd0 : GoFunc) (N : Nat) (hcfg : 0 ≤ sint.Z cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        ownToks d.γB.wb (N + 2) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d⌝ ∗
        txn.isKV (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.store.ty) #s) s γ ∗ mvcc.hookIs γ Pk #f ∗
        ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.storeReader s γ) ∗
        txn.soleWriter γ [[], []] ∗ txn.storeWTs γ N ∗ mvcc.storeCloser s γ }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hhk, #Hsz, Hv, Hncmp, Hrg, Hw, Hrts, Hlrd, #Hle, Hro⟩ HΦ
  rw [show N + 2 = (N + 1) + 1 by omega]
  icases ownToks_add_1 1 (N + 1) d.γB.wb $$ Hw with ⟨Hw, Hw1⟩
  icases ownToks_add_1 1 N d.γB.wb $$ Hw with ⟨Hw, Hw2⟩
  iapply wp_fupd
  wp_apply (mvcc_NewStore_backend lg le cfg d hP γb γl Pk f hf rd0 hcfg hrb) $$ [Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd Hro]
    as %s ⟨%γ, %Hγ, #Hst, -, Hcok, Hhk', -, Hrds, Htoks, #Hc, Hcl, -, Hright⟩
  · iframe #; iframe Hv Hncmp Hrg Hrts Hlrd Hro
    unfold backend.wbTok
    iframe Hw1 Hw2
  -- the apply thread's store is never compacted (the compaction is not in the server's model):
  -- the compaction right's half given up, the readers those of a never-compacted store (as the
  -- watchable store's `newWatchableStore` does)
  imod mvcc.crevFrozen_alloc γ ⊤ $$ Hright with #Hfrz
  ihave Hrds := mvcc.storeReaders_of s γ _ $$ [$Hfrz $Hrds]
  imodintro
  iapply HΦ
  iexists γ
  isplitr
  · ipureintro; exact ⟨Hγ.1, Hγ.2.1, Hγ.2.2.1⟩
  iframe Hhk' Hrds Hcl Hcok
  isplitr
  · iunfold txn.isKV; ileft; iframe Hst; isplitr; · ipureintro; rfl
    ipureintro; exact Hγ.2.2.2
  isplitl [Htoks]
  · iapply txn.soleWriter_of_NewStore γ hrb; iframe Htoks Hc
  unfold txn.storeWTs
  rw [Hγ.2.2.1]
  iexact Hw

/-- **The server's KV over the real backend: `mvcc.New`'s watchable store** (unit N4, D14a/b):
`mvcc.New` on a fresh backend of the real instance `d`, before the post-lock hook is installed
(the store's contract names the backend's hook slot, `storeBackend`), gives the KV rows of the
server's construction premise for the watchable store `ws` over its inner store `st`: the txn
package's `isKV` (the watchable store), the inner store's read view (the watchable store points
it at itself), the KV's writer at `NewStore`'s log `[[], []]` (`kvWriter`: the sole writer and
the writer's half of the notified log), `N` write tokens, the recorded batch-lock invariant
(`hookInit`: `hookIs` once the server freezes the hook, `hookIs_of_init`), the certificate map's
authority; and the watch side's (the watchable store, its watch tokens, its readers but the two
loops', the right to close it). The index's names `γi` and the map `γok` are the caller's (D13a). -/
theorem server_kv_watchable (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF) (f : val)
    (rd0 : GoFunc) (N : Nat) (γi : mvcc.IdxNames) (γok : GName) (M : auth.AuthMode) (hcfg : 0 ≤ sint.Z cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        ownToks d.γB.wb (N + 2) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
        mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (ws : Loc), RET #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws);
        ∃ (st : Loc) (γw : mvcc.WsNames),
        ⌜γw.st.bucket = γb ∧ γw.st.leases = γl ∧ γw.st.kb = some d ∧ γw.st.idx = γi ∧
          γw.st.cok = γok⌝ ∗
        txn.isKV (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws) st γw.st ∗
        (∃ rv : Loc, st.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv st γw.st) ∗
        mvcc.hookInit γw.st Pk f ∗ txn.kvWriter st γw.st [[], []] ∗ txn.storeWTs γw.st N ∗
        ghostMapAuth γw.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        mvcc.isWatchableStore ws st γw ∗ mvcc.watchToks γw (2 ^ 63 - 3) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (),
          mvcc.watchReader ws st γw) ∗
        mvcc.wsCloser ws st γw.st ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd ws st γw) ∗ auth.modeTag γw.tag M }} := by
  iintro %Φ Hpre HΦ
  iapply (server_kv_watchable_of mvcc.wp_New backend.backend.wp_ConcurrentReadTx
      backend.backend.wp_ReadTx backend.backend.wp_BatchTx backend.backend.wp_ForceCommit
      backend.backend.wp_Size backend.backend.wp_SizeInUse
      backend.concurrentReadTx.wp_RLock backend.concurrentReadTx.wp_RUnlock
      backend.concurrentReadTx.wp_UnsafeRange backend.readTx.wp_RLock backend.readTx.wp_RUnlock
      backend.readTx.wp_UnsafeRange backend.batchTxBuffered.wp_LockInsideApply
      backend.batchTxBuffered.wp_LockOutsideApply backend.batchTxBuffered.wp_UnsafeSeqPut
      backend.batchTxBuffered.wp_Unlock backend.batchTxBuffered.wp_UnsafeRange
      backend.batchTxBuffered.wp_UnsafeCreateBucket
      backend.batchTxBuffered.wp_UnsafeDelete schema.bucket.wp_ID schema.bucket.wp_Name
      schema.bucket.wp_IsSafeRangeBucket lg le cfg d hP γb γl Pk f rd0 N γi γok M hcfg hrb) $$ [Hpre]
  · iexact Hpre
  inext
  iintro %ws ⟨%st, %γw, %Hγ, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, -, Hrd, H11⟩
  iapply HΦ
  iexists st, γw
  iframe
  ipureintro; exact Hγ

/-- **The consistent index's pre-commit hook over the real backend** (unit 7, 2026-10-13): on
the real backend's batch transaction, in the hook's window (`hookPre`), the consistent index's
`UnsafeSave` with the server's batch-lock resource (`batchLockInv γA (metaTM γ P)`: the stored
index's mirror, the meta keys as the client's half of the hook's own keys, the lock's token) is a
hook step (`hookStep`) and gives the resource back, the meta keys at what the commit persists.
For backend parameters whose hook's own keys are the consistent index's two (`ciKeys`: a real
instance's, `ciKeys_of`, for a hook's bound of at least 2). Its trust base: bbolt's contract,
the backend's and schema's, and the consistent index's (`verify.Verify`, `binary`). -/
theorem cindex_hook_backend (γA : ApplyNames) (ci : Loc) (γ : backend.BNames) (P : backend.BParams)
    (W Pk : IProp GF) (b t : Loc) (hP : ciKeys P) (st : backend.BSess) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      backend.isBackend γ P W Pk b ∗ backend.bF go!"batchTx" b ↦□ t ∗ isCI ci γA.ci ∗
      inv applyN (consInv γA) ∗ applyRegd γA ⊢
      {{ backend.batchLocked γ P b st ∗ batchLockInv γA (metaTM γ P) ∗ ⌜backend.hookPre P st⌝ }}
        (App (Val (ci @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!! go!"UnsafeSave"))
          (Val #(interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t)))
      {{ RET #(); ∃ st' : backend.BSess, backend.batchLocked γ P b st' ∗
          batchLockInv γA (metaTM γ P) ∗ ⌜backend.hookStep P st st'⌝ }} :=
  ci_hook_backend consistentIndex.wp_UnsafeSave backend.batchTxBuffered.wp_UnsafePut
    backend.batchTxBuffered.wp_UnsafeRange schema.bucket.wp_ID schema.bucket.wp_Name
    schema.bucket.wp_IsSafeRangeBucket γA ci γ P W Pk b t hP st

/-- The backend's hook contract (`hookFnSpec`, what `NewHooks` wraps into the backend's
`hooksSpec`) of any hook function that runs the consistent index's `UnsafeSave` on the batch
transaction (etcd's `BackendHooks.OnPreCommitUnsafe` does, then saves the `confState` when it
is dirty: `storage/hooks.go`, not translated), the hooks' resource the server's batch-lock
resource. -/
theorem cindex_hookFnSpec (γA : ApplyNames) (ci : Loc) (γ : backend.BNames) (P : backend.BParams)
    (W Pk : IProp GF) (b t : Loc) (hP : ciKeys P) (f : GoFunc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      backend.isBackend γ P W Pk b ∗ backend.bF go!"batchTx" b ↦□ t ∗ isCI ci γA.ci ∗
      inv applyN (consInv γA) ∗ regdOrLink γA γ ∗
      □ (∀ (v : val) (Ψ : val → IProp GF),
          WP (App (Val (ci @!! go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!! go!"UnsafeSave"))
            (Val v)) {{ Ψ }} -∗
          WP (App (Val #f) (Val v)) {{ Ψ }}) ⊢
      backend.hookFnSpec γ P (batchLockInv γA (metaTM γ P)) b t f :=
  ci_hookFnSpec consistentIndex.wp_UnsafeSave backend.batchTxBuffered.wp_UnsafePut
    backend.batchTxBuffered.wp_UnsafeRange schema.bucket.wp_ID schema.bucket.wp_Name
    schema.bucket.wp_IsSafeRangeBucket γA ci γ P W Pk b t hP f

/-- **The backend over the server's hooks** (unit 8, 2026-10-13): a backend whose `hooks` field
is the server's `BackendHooks` `bh` over the consistent index `ci` (`isBackendNH`: every fact of
`isBackend` but the hooks' contract; `isBackendHooks`: `NewBackendHooks`' result), the hooks'
resource the server's batch-lock resource, is `isBackend`: the hooks' contract is derived from
`BackendHooks.OnPreCommitUnsafe` (the consistent index's save, then the `confState`'s, a put
into `Meta`), by Löb induction. For backend parameters whose hook's own keys are the consistent
index's (`ciKeys`) and that let the hook save the `confState` (`hooksParams`: `Meta` a hook's
bucket, its `confState` key not a hook's own key, `hookMax ≥ 3`). Its trust base adds
`schema.MustUnsafeSaveConfStateToBackend` (its `json.Marshal`) to the consistent index's. -/
theorem backend_server_hooks (γA : ApplyNames) (ci : Loc) (γ : backend.BNames)
    (P : backend.BParams) (W : IProp GF) (b bh lgh : Loc) (hP : ciKeys P)
    (hH : storage.hooksParams P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      storage.isBackendHooks bh
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty,
          #ci⟩ lgh ∗
      backend.isBackendNH γ P W (batchLockInv γA (metaTM γ P)) b (storage.hooksIface bh) ∗
      isCI ci γA.ci ∗ inv applyN (consInv γA) ∗ regdOrLink γA γ ⊢
      backend.isBackend γ P W (batchLockInv γA (metaTM γ P)) b :=
  backend_server_hooks_of storage.BackendHooks.wp_OnPreCommitUnsafe consistentIndex.wp_UnsafeSave
    backend.batchTxBuffered.wp_UnsafePut backend.batchTxBuffered.wp_UnsafeRange schema.bucket.wp_ID
    schema.bucket.wp_Name schema.bucket.wp_IsSafeRangeBucket γA ci γ P W b bh lgh hP hH

/-- **The apply thread's KV over the real backend, its hooks the server's** (unit 8,
2026-10-13): `server_kv_backend` with the backend's hooks' contract derived
(`backend_server_hooks`) rather than assumed: the backend made for the real instance `d` with
the server's `BackendHooks` `bh` over the consistent index `ci` (`isBackendNH`, the creator's:
the backend's constructor is not proved), the hooks' resource the server's batch-lock resource
`batchLockInv γA (metaTM d.γB d.P)`; `bh` as `NewBackendHooks` makes it (`isBackendHooks`), the
consistent index (`isCI`) and the apply thread's invariant (`consInv`); and the parameters'
facts (`ciKeys`, `hooksParams`). The lessor is the real one at `lp` (`lease.lessorInv`: mvcc's
`isLessor` derived from its proofs, `lease.isLessor_of_lessorInv`; unit 8), with a reader slot of
its lock for the store. The other premises are `server_kv_backend`'s. -/
theorem server_kv_backend_hooks (lg lp : Loc)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (hci : ciKeys d.P)
    (hH : storage.hooksParams d.P) (γb γl : GName) (γA : ApplyNames) (ci bh lgh : Loc)
    (f : GoFunc) (hf : f ≠ func.nil) (rd0 : GoFunc) (N : Nat) (hcfg : 0 ≤ sint.Z cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
        backend.isBackendNH d.γB d.P (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) d.be
          (storage.hooksIface bh) ∗
        storage.isBackendHooks bh
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty,
            #ci⟩ lgh ∗
        isCI ci γA.ci ∗ inv applyN (consInv γA) ∗ regdOrLink γA d.γB ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        ownToks d.γB.wb (N + 2) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
        lease.lessorInv lp γl ∗ lease.lessorRdOf γl ∗ lease.rdOwn γl rd0 }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #(lease.lessorIface lp))) (Val #cfg))
    {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d⌝ ∗
        txn.isKV (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.store.ty) #s) s γ ∗
        mvcc.hookIs γ (batchLockInv γA (metaTM d.γB d.P)) #f ∗
        ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.storeReader s γ) ∗
        txn.soleWriter γ [[], []] ∗ txn.storeWTs γ N ∗ mvcc.storeCloser s γ }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hspkg, #Hcpkg, #Hnh, #Hh, #Hci, #Hinv, #Hrl, #Hhk, #Hsz, Hv,
    Hncmp, Hrg, Hw, Hrts, #Hlpkg, #Hlinv, Hlrd, Hro⟩ HΦ
  ihave #Hb := backend_server_hooks γA ci d.γB d.P (mvcc.lateW d.gx) d.be bh lgh hci hH $$
    [$Hspkg $Hbpkg $Hsch $Hcpkg $Hh $Hnh $Hci $Hinv $Hrl]
  ihave #Hle := lease.isLessor_of_lessorInv lease.lessor.wp_GetLease lease.lessor.wp_Attach
    lease.lessor.wp_Detach lease.lessor.wp_SetRangeDeleter lp γl $$ [$Hlpkg $Hlinv]
  iapply (server_kv_backend lg (lease.lessorIface lp) cfg d hP γb γl
    (batchLockInv γA (metaTM d.γB d.P)) f hf rd0 N hcfg hrb) $$ [Hv Hncmp Hrg Hw Hrts Hlrd Hro] HΦ
  iframe #
  iframe Hv Hncmp Hrg Hw Hrts Hlrd Hro

/-- **The lessor's contracts, of the real lessor** (unit 8, 2026-10-13): the lessor at `lp`
(`lease.lessorInv`) is the txn package's `isTxnLessor` (mvcc's `isLessor`, and `Lookup` for the
lease owner), from the proofs of its `GetLease`, `Attach`, `Detach`, `SetRangeDeleter` and
`Lookup`. -/
theorem lessor_txn_contract (lp : Loc) (γl : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lease.lessorInv lp γl ⊢
      txn.isTxnLessor (lease.lessorIface lp) γl :=
  lease.isTxnLessor_of_lessorInv lease.lessor.wp_GetLease lease.lessor.wp_Attach
    lease.lessor.wp_Detach lease.lessor.wp_SetRangeDeleter lease.lessor.wp_Lookup lp γl

/-- **The server's lessor contract, of the real lessor** (unit 9, 2026-10-13): the lessor at `lp`
(`lease.lessorInv`, its configuration, its `expiredC` at the grant guard `False`, D19n, D45)
meets `lessorOk`: `ExpiredLeasesC` proved,
`Promote` and `Demote` the trust boundary (`lease.lessor.Promote.wp_proof`,
`lease.lessor.Demote.wp_proof`). -/
theorem lessor_server_contract (lp : Loc) (γl : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lease.lessorInv lp γl ∗
      lease.lessorCfg lp ∗ lease.lessorExpiredC lp srvGrantGuard ⊢
      lessorOk (lease.lessorIface lp) :=
  lessorOk_of_lessorInv lease.lessor.wp_Promote lease.lessor.wp_Demote
    lease.lessor.wp_ExpiredLeasesC lp γl

/-- **The apply package's lessor contract, of the real lessor** (unit 9, 2026-10-13): the lessor
at `lp` (`lease.lessorInv`, its configuration, its backend's contract for the `Lease` bucket,
`lease.lessorBackend`) meets `apply.isApplyLessor`'s `isTxnLessor`, `Grant` and `Checkpoint`
clauses, from their proofs; its `Revoke` and `Lookup` clauses are the premises
(`apply.isApplyLessor_of_lessorInv`). -/
theorem lessor_apply_contract (lp s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RW : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp γ.leases ∗ lease.lessorCfg lp ∗
      lease.lessorBackend lp P f iprop(mvcc.storeWT γ ∗ RW) (mvcc.storeRT γ) ∗
      □ (∀ id : w64,
        {{ True }} (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty
          @!! go!"Lookup")) (Val #id))
        {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ EtcdGrove.apply.leaseIs l id }}) ⊢
      EtcdGrove.apply.isApplyLessor (lease.lessorIface lp) s γ P f RW :=
  EtcdGrove.apply.isApplyLessor_of_lessorInv lease.lessor.wp_GetLease lease.lessor.wp_Attach
    lease.lessor.wp_Detach lease.lessor.wp_SetRangeDeleter lease.lessor.wp_Lookup
    lease.lessor.wp_Grant lease.lessor.wp_Checkpoint lease.Lease.wp_TTL lp s γ P f RW

/-- **The auth store's admin side as model steps, of the real store** (the auth plan's S4, its
apply part, 2026-10-24; `apply/AuthSteps.lean`): the store at `st` (`auth.authInv st R M`) has
`apply.isAuthSteps` with its write resource `auth.authWR st M P f T` and the admin side's share of
the token provider `auth.tpAdmin st M` (S5d), from S4's proofs of
`AuthEnable`, `AuthDisable`, `UserAdd`, `UserDelete`, `UserChangePassword`, `RoleAdd`, and S4b's of
`UserRevokeRole`, `RoleRevokePermission`, `RoleDelete`, S4c's of `UserGrantRole` and S4d's of
`RoleGrantPermission`. -/
theorem auth_apply_steps (st : Loc) (R : IProp GF) (M : auth.AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      EtcdGrove.apply.isAuthSteps (auth.authIface st) P f M
        iprop(auth.authWR st M P f T ∗ auth.tpAdmin st M) :=
  EtcdGrove.apply.isAuthSteps_of_authInv auth.authStore.wp_AuthEnable auth.authStore.wp_AuthDisable
    (auth.authStore.UserAdd.wp_sure auth.authStore.wp_commitRevision
      auth.authStore.wp_refreshRangePermCache auth.authStore.wp_selectPassword zap.wp_String
      zap.Logger.wp_Info)
    auth.authStore.wp_UserDelete auth.authStore.wp_UserChangePassword
    auth.authStore.wp_RoleAdd auth.authStore.wp_UserRevokeRole auth.authStore.wp_RoleRevokePermission
    auth.authStore.wp_RoleDelete auth.authStore.wp_UserGrantRole auth.authStore.wp_RoleGrantPermission
    st R M P f T

/-- **The apply layer's admin requests perform the model's step** (`apply/AuthSteps.lean`):
`applierV3backend.X` from the backend's options' `isAuthSteps`, the admin side's authority and
the store's write resource. -/
theorem apply_AuthEnable_step :
    EtcdGrove.apply.applierV3backend.AuthEnable.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.AuthEnable.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_AuthDisable_step :
    EtcdGrove.apply.applierV3backend.AuthDisable.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.AuthDisable.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_UserAdd_step :
    EtcdGrove.apply.applierV3backend.UserAdd.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserAdd.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_UserDelete_step :
    EtcdGrove.apply.applierV3backend.UserDelete.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserDelete.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_UserChangePassword_step :
    EtcdGrove.apply.applierV3backend.UserChangePassword.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserChangePassword.wp_step
    EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_RoleAdd_step :
    EtcdGrove.apply.applierV3backend.RoleAdd.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleAdd.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

/-- **The token binding at the server's guards** (the auth plan's E1, `AuthBound.lean`): the
server's `AuthInfoFromCtx` returns an auth info bound to the request's token (or from the TLS
fallback), and the member operations' admin guard checks such a principal, over a store with the
bound request side (`srvAuthBound`, of the real store once `NewAuthStore` is proved). -/
theorem server_AuthInfoFromCtx_bound :
    EtcdServer.AuthInfoFromCtx.boundSpec (GF := GF) (hG := hG) :=
  EtcdServer.AuthInfoFromCtx_bound EtcdServer.wp_AuthStore

theorem server_membership_guard_bound :
    EtcdServer.checkMembershipOperationPermission.boundSpec (GF := GF) (hG := hG) :=
  EtcdServer.checkMembershipOperationPermission_bound EtcdServer.wp_AuthStore

theorem server_requireAuthInfo_bound :
    EtcdServer.requireAuthInfo.boundSpec (GF := GF) (hG := hG) :=
  EtcdServer.requireAuthInfo_bound EtcdServer.wp_AuthStore

theorem apply_UserGrantRole_step :
    EtcdGrove.apply.applierV3backend.UserGrantRole.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserGrantRole.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_RoleGrantPermission_step :
    EtcdGrove.apply.applierV3backend.RoleGrantPermission.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleGrantPermission.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_UserRevokeRole_step :
    EtcdGrove.apply.applierV3backend.UserRevokeRole.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserRevokeRole.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_RoleRevokePermission_step :
    EtcdGrove.apply.applierV3backend.RoleRevokePermission.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleRevokePermission.wp_step
    EtcdGrove.apply.applierV3backend.wp_newHeader

theorem apply_RoleDelete_step :
    EtcdGrove.apply.applierV3backend.RoleDelete.stepSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleDelete.wp_step EtcdGrove.apply.applierV3backend.wp_newHeader

/-- **The admin requests in the mode `on γa`, from the receipts' budget**
(the auth plan's E2l, `apply/AuthFuel.lean`): the step's premises from the admin side's fuel and
one receipt of the apply thread's, the fuel given back with the step's result. -/
theorem apply_UserAdd_fuel :
    EtcdGrove.apply.applierV3backend.UserAdd.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserAdd.wp_fuel apply_UserAdd_step

theorem apply_RoleAdd_fuel :
    EtcdGrove.apply.applierV3backend.RoleAdd.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleAdd.wp_fuel apply_RoleAdd_step

theorem apply_UserGrantRole_fuel :
    EtcdGrove.apply.applierV3backend.UserGrantRole.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserGrantRole.wp_fuel apply_UserGrantRole_step

theorem apply_RoleGrantPermission_fuel :
    EtcdGrove.apply.applierV3backend.RoleGrantPermission.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleGrantPermission.wp_fuel apply_RoleGrantPermission_step

theorem apply_AuthEnable_fuel :
    EtcdGrove.apply.applierV3backend.AuthEnable.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.AuthEnable.wp_fuel apply_AuthEnable_step

theorem apply_UserDelete_fuel :
    EtcdGrove.apply.applierV3backend.UserDelete.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserDelete.wp_fuel apply_UserDelete_step

theorem apply_UserChangePassword_fuel :
    EtcdGrove.apply.applierV3backend.UserChangePassword.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserChangePassword.wp_fuel apply_UserChangePassword_step

theorem apply_UserRevokeRole_fuel :
    EtcdGrove.apply.applierV3backend.UserRevokeRole.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserRevokeRole.wp_fuel apply_UserRevokeRole_step

theorem apply_RoleRevokePermission_fuel :
    EtcdGrove.apply.applierV3backend.RoleRevokePermission.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleRevokePermission.wp_fuel apply_RoleRevokePermission_step

theorem apply_RoleDelete_fuel :
    EtcdGrove.apply.applierV3backend.RoleDelete.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleDelete.wp_fuel apply_RoleDelete_step

theorem apply_AuthDisable_fuel :
    EtcdGrove.apply.applierV3backend.AuthDisable.fuelSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.AuthDisable.wp_fuel apply_AuthDisable_step

end backend

#print axioms Perennial.EtcdGrove.lessor_server_contract
#print axioms Perennial.EtcdGrove.lessor_apply_contract
#print axioms Perennial.EtcdGrove.auth_apply_steps
#print axioms Perennial.EtcdGrove.apply_AuthEnable_step
#print axioms Perennial.EtcdGrove.apply_AuthDisable_step
#print axioms Perennial.EtcdGrove.apply_UserAdd_step
#print axioms Perennial.EtcdGrove.apply_UserDelete_step
#print axioms Perennial.EtcdGrove.apply_UserChangePassword_step
#print axioms Perennial.EtcdGrove.apply_RoleAdd_step
#print axioms Perennial.EtcdGrove.server_AuthInfoFromCtx_bound
#print axioms Perennial.EtcdGrove.server_membership_guard_bound
#print axioms Perennial.EtcdGrove.server_requireAuthInfo_bound
#print axioms Perennial.EtcdGrove.apply_UserGrantRole_step
#print axioms Perennial.EtcdGrove.apply_RoleGrantPermission_step
#print axioms Perennial.EtcdGrove.apply_UserRevokeRole_step
#print axioms Perennial.EtcdGrove.apply_RoleRevokePermission_step
#print axioms Perennial.EtcdGrove.apply_RoleDelete_step
#print axioms Perennial.EtcdGrove.apply_UserAdd_fuel
#print axioms Perennial.EtcdGrove.apply_RoleAdd_fuel
#print axioms Perennial.EtcdGrove.apply_UserGrantRole_fuel
#print axioms Perennial.EtcdGrove.apply_RoleGrantPermission_fuel
#print axioms Perennial.EtcdGrove.apply_AuthEnable_fuel
#print axioms Perennial.EtcdGrove.apply_UserDelete_fuel
#print axioms Perennial.EtcdGrove.apply_UserChangePassword_fuel
#print axioms Perennial.EtcdGrove.apply_UserRevokeRole_fuel
#print axioms Perennial.EtcdGrove.apply_RoleRevokePermission_fuel
#print axioms Perennial.EtcdGrove.apply_RoleDelete_fuel
#print axioms Perennial.EtcdGrove.apply_AuthDisable_fuel
#print axioms Perennial.EtcdGrove.lessor_txn_contract
#print axioms Perennial.EtcdGrove.server_kv_backend
#print axioms Perennial.EtcdGrove.server_kv_watchable

section latest
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The apply thread's permission check at the latest state** (the auth plan's E2r,
`auth/Latest.lean`): with the admin side's authority `hs` and its halves of the flag and the
cache tied to the latest state (`latestTie`), `isOpPermitted`'s verdict is the latest state's
(`permVerdictL`), every callee linked. -/
theorem auth_op_permitted_latest :
    auth.authStore.isOpPermitted.specL (GF := GF) (hG := hG) :=
  auth.authStore.isOpPermitted.wp_latest auth.authStore.IsAuthEnabled.wp_latest
    auth.authStore.wp_Revision zap.wp_Uint64 zap.wp_ByteString zap.wp_Error zap.Logger.wp_Warn
    zap.wp_String zap.Logger.wp_Error auth.wp_hasRootRole auth.authStore.lockedReadTx.wp_latest
    (auth.authStore.isRangeOpPermitted.wp_latest zap.wp_String zap.Logger.wp_Error
      auth.wp_checkKeyInterval auth.wp_checkKeyPoint)

/-- **`IsPutPermitted`, `IsRangePermitted`, `IsDeleteRangePermitted` on the apply thread at the
latest state** (the auth plan's E2r): the verdict of their one permission at the latest state
(`permVerdictL`; for a request of the cache's shape, `kvGranted`'s form, `auth.permVerdictL_granted`). -/
theorem auth_put_permitted_latest :
    auth.authStore.IsPutPermitted.specL (GF := GF) (hG := hG) :=
  auth.authStore.IsPutPermitted.wp_latest auth_op_permitted_latest

theorem auth_range_permitted_latest :
    auth.authStore.IsRangePermitted.specL (GF := GF) (hG := hG) :=
  auth.authStore.IsRangePermitted.wp_latest auth_op_permitted_latest

theorem auth_delete_range_permitted_latest :
    auth.authStore.IsDeleteRangePermitted.specL (GF := GF) (hG := hG) :=
  auth.authStore.IsDeleteRangePermitted.wp_latest auth_op_permitted_latest

end latest

#print axioms Perennial.EtcdGrove.auth_op_permitted_latest
#print axioms Perennial.EtcdGrove.auth_put_permitted_latest
#print axioms Perennial.EtcdGrove.auth_range_permitted_latest
#print axioms Perennial.EtcdGrove.auth_delete_range_permitted_latest

section readLb
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The store's locked read transaction no older than a published index** (the auth plan's E3g,
`auth/ReadLb.lean`): a reader holding a lower bound `i` of the history's published index
(`authPubLbM`) gets a read transaction at a state recorded at an index at least `i`, over the
backend's read contract's lower-bound clause. -/
theorem auth_locked_read_tx_lb :
    auth.authStore.lockedReadTx.specLb (GF := GF) (hG := hG) :=
  auth.authStore.lockedReadTx.wp_lb

/-- **The store's fields read no older than a published index** (the auth plan's E3h,
`auth/Fresh.lean`, `auth/FreshCheck.lean`): with a reader's lower bound `n`, the revision and the
flag are a state's no older than `n` (the store's freshness, `revFresh`), and the permission checks'
verdicts are at states no older than `n` (`permVerdictFrom`). -/
theorem auth_revision_lb : auth.authStore.Revision.specLb (GF := GF) :=
  auth.authStore.Revision.wp_lb

theorem auth_enabled_lb : auth.authStore.IsAuthEnabled.specLb (GF := GF) :=
  auth.authStore.IsAuthEnabled.wp_lb

theorem auth_range_op_permitted_lb : auth.authStore.isRangeOpPermitted.specLb (GF := GF) :=
  auth.authStore.isRangeOpPermitted.wp_lb zap.wp_String zap.Logger.wp_Error
    auth.wp_checkKeyInterval auth.wp_checkKeyPoint

theorem auth_op_permitted_lb : auth.authStore.isOpPermitted.specLb (GF := GF) :=
  auth.authStore.isOpPermitted.wp_lb auth_enabled_lb auth_revision_lb zap.wp_Uint64
    zap.wp_ByteString zap.wp_Error zap.Logger.wp_Warn zap.wp_String zap.Logger.wp_Error
    auth.wp_hasRootRole auth.authStore.lockedReadTx.wp_lb auth_range_op_permitted_lb

/-- **The read wrappers no older than a reader's lower bound** (the auth plan's E3j,
`auth/FreshWrap.lean`): `IsRangePermitted` (the read path's check), `IsPutPermitted`,
`IsDeleteRangePermitted` over `isOpPermitted.specLb`, every callee linked. -/
theorem auth_range_permitted_lb : auth.authStore.IsRangePermitted.specLb (GF := GF) :=
  auth.authStore.IsRangePermitted.wp_lb auth_op_permitted_lb

theorem auth_put_permitted_lb : auth.authStore.IsPutPermitted.specLb (GF := GF) :=
  auth.authStore.IsPutPermitted.wp_lb auth_op_permitted_lb

theorem auth_delete_range_permitted_lb : auth.authStore.IsDeleteRangePermitted.specLb (GF := GF) :=
  auth.authStore.IsDeleteRangePermitted.wp_lb auth_op_permitted_lb

end readLb

#print axioms Perennial.EtcdGrove.auth_locked_read_tx_lb
#print axioms Perennial.EtcdGrove.auth_revision_lb
#print axioms Perennial.EtcdGrove.auth_enabled_lb
#print axioms Perennial.EtcdGrove.auth_range_op_permitted_lb
#print axioms Perennial.EtcdGrove.auth_op_permitted_lb
#print axioms Perennial.EtcdGrove.auth_range_permitted_lb
#print axioms Perennial.EtcdGrove.auth_put_permitted_lb
#print axioms Perennial.EtcdGrove.auth_delete_range_permitted_lb

section latestApply
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`IsAdminPermitted` on the apply thread at the latest state** (the auth plan's E2s,
`auth/LatestAdmin.lean`): exact both ways (`adminVerdictL`), every callee linked. -/
theorem auth_admin_permitted_latest :
    auth.authStore.IsAdminPermitted.specL (GF := GF) (hG := hG) :=
  auth.authStore.IsAdminPermitted.wp_latest auth.authStore.IsAuthEnabled.wp_latest
    auth.authStore.lockedReadTx.wp_latest auth.wp_hasRootRole

/-- **The real store's checks at the latest state, as the apply package states them** (the auth
plan's E2s, `apply/AuthLatest.lean`): `isAuthStoreL` of the store's interface, with the reader
resource `authRd` and the apply thread's `latestRes`. -/
theorem apply_auth_store_latest (st : Loc) (R : IProp GF) (M : auth.AuthMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      EtcdGrove.apply.isAuthStoreL (auth.authIface st) (auth.authRd st R M) M (auth.latestRes st M) :=
  EtcdGrove.apply.isAuthStoreL_of_authInv auth_put_permitted_latest auth_range_permitted_latest
    auth_delete_range_permitted_latest auth_admin_permitted_latest st R M

/-- **The auth applier's KV methods on the apply thread** (the auth plan's E2s,
`apply/AuthApplyLatest*.lean`): the outcome decided at the latest state, a rejection with a checked
permission refused there or the inner chain's outcome with every checked permission granted
(`authOutL`; for `Put` and `Txn` with the lessor finding no lease). -/
theorem apply_range_latest :
    EtcdGrove.apply.authApplierV3.Range.specL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.authApplierV3.Range.wp_latest

theorem apply_delete_range_latest :
    EtcdGrove.apply.authApplierV3.DeleteRange.specL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.authApplierV3.DeleteRange.wp_latest

theorem apply_check_put_latest :
    EtcdGrove.apply.checkPutAuth.specL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.checkPutAuth.wp_latest EtcdGrove.apply.checkLeasePuts.wp_nil

theorem apply_put_latest :
    EtcdGrove.apply.authApplierV3.Put.specL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.authApplierV3.Put.wp_latest apply_check_put_latest

theorem apply_txn_latest :
    EtcdGrove.apply.authApplierV3.Txn.specL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.authApplierV3.Txn.wp_latest
    (EtcdGrove.apply.CheckTxnAuth.wp_latest
      (EtcdGrove.apply.checkTxnPermission.wp_latest apply_check_put_latest))

/-- **The admin operations keep the apply thread's tie** (the auth plan's E2s, `auth/LatestTie.lean`):
each operation's spec with the admin side's halves of the flag and the cache exposed
(`authWRx`), carried from the latest state before to the latest state after (`tieStep`), every
callee linked. -/
theorem auth_auth_enable_tie :
    auth.authStore.AuthEnable.specT (GF := GF) (hG := hG) :=
  auth.authStore.AuthEnable.wp_tie auth.authStore.wp_refreshRangePermCache auth.authStore.wp_setRevision auth.wp_hasRootRole zap.Logger.wp_Info

theorem auth_auth_disable_tie :
    auth.authStore.AuthDisable.specT (GF := GF) (hG := hG) :=
  auth.authStore.AuthDisable.wp_tie auth.authStore.wp_commitRevision zap.Logger.wp_Info

theorem auth_user_add_tie :
    auth.authStore.UserAdd.specT (GF := GF) (hG := hG) :=
  auth.authStore.UserAdd.wp_tie auth.authStore.wp_commitRevision auth.authStore.wp_refreshRangePermCache auth.authStore.wp_selectPassword zap.wp_String zap.Logger.wp_Info

theorem auth_user_delete_tie :
    auth.authStore.UserDelete.specT (GF := GF) (hG := hG) :=
  auth.authStore.UserDelete.wp_tie auth.authStore.wp_commitRevision auth.authStore.wp_refreshRangePermCache zap.wp_String zap.wp_Strings zap.Logger.wp_Error zap.Logger.wp_Info

theorem auth_user_change_password_tie :
    auth.authStore.UserChangePassword.specT (GF := GF) (hG := hG) :=
  auth.authStore.UserChangePassword.wp_tie auth.authStore.wp_commitRevision auth.authStore.wp_refreshRangePermCache auth.authStore.wp_selectPassword zap.wp_String zap.wp_Strings zap.Logger.wp_Info

theorem auth_user_grant_role_tie :
    auth.authStore.UserGrantRole.specT (GF := GF) (hG := hG) :=
  auth.authStore.UserGrantRole.wp_tie auth.authStore.wp_commitRevision auth.authStore.wp_refreshRangePermCache zap.wp_String zap.wp_Strings zap.Logger.wp_Warn zap.Logger.wp_Info

theorem auth_user_revoke_role_tie :
    auth.authStore.UserRevokeRole.specT (GF := GF) (hG := hG) :=
  auth.authStore.UserRevokeRole.wp_tie auth.authStore.wp_commitRevision auth.authStore.wp_refreshRangePermCache zap.wp_String zap.wp_Strings zap.Logger.wp_Error zap.Logger.wp_Info

theorem auth_role_add_tie :
    auth.authStore.RoleAdd.specT (GF := GF) (hG := hG) :=
  auth.authStore.RoleAdd.wp_tie auth.authStore.wp_commitRevision zap.wp_String zap.Logger.wp_Info

theorem auth_role_delete_tie :
    auth.authStore.RoleDelete.specT (GF := GF) (hG := hG) :=
  auth.authStore.RoleDelete.wp_tie auth.authStore.wp_commitRevision auth.authStore.wp_refreshRangePermCache zap.wp_String zap.Logger.wp_Error zap.Logger.wp_Info

theorem auth_role_grant_permission_tie :
    auth.authStore.RoleGrantPermission.specT (GF := GF) (hG := hG) :=
  auth.authStore.RoleGrantPermission.wp_tie auth.authStore.wp_commitRevision auth.authStore.wp_refreshRangePermCache auth.wp_isValidPermissionRange zap.wp_String zap.wp_ByteString zap.Logger.wp_Info

theorem auth_role_revoke_permission_tie :
    auth.authStore.RoleRevokePermission.specT (GF := GF) (hG := hG) :=
  auth.authStore.RoleRevokePermission.wp_tie auth.authStore.wp_commitRevision auth.authStore.wp_refreshRangePermCache zap.wp_String zap.Logger.wp_Info


/-- **The real store's five `SetUp` admin steps with the tie** (the auth plan's E2v,
`apply/AuthStepsX.lean`): `isAuthStepsX` with the halves tied to the history (`auth.tieRes`),
from E2s's tie-keeping specs. -/
theorem apply_auth_steps_tie (st : Loc) (R : IProp GF) (M : auth.AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      EtcdGrove.apply.isAuthStepsX (auth.authIface st) P f M (auth.tieRes st M)
        iprop(auth.authWB st M P f T ∗ auth.tpAdmin st M) :=
  EtcdGrove.apply.isAuthStepsX_of_authInvT auth_auth_enable_tie
    (auth.authStore.UserAdd.wp_tieSure auth.authStore.wp_commitRevision
      auth.authStore.wp_refreshRangePermCache auth.authStore.wp_selectPassword zap.wp_String
      zap.Logger.wp_Info) auth_role_add_tie
    auth_user_grant_role_tie auth_role_grant_permission_tie st R M P f T

theorem apply_UserAdd_fuelX :
    EtcdGrove.apply.applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserAdd.wp_fuelX
    (EtcdGrove.apply.applierV3backend.UserAdd.wp_stepX EtcdGrove.apply.applierV3backend.wp_newHeader)

theorem apply_RoleAdd_fuelX :
    EtcdGrove.apply.applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleAdd.wp_fuelX
    (EtcdGrove.apply.applierV3backend.RoleAdd.wp_stepX EtcdGrove.apply.applierV3backend.wp_newHeader)

theorem apply_UserGrantRole_fuelX :
    EtcdGrove.apply.applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.UserGrantRole.wp_fuelX
    (EtcdGrove.apply.applierV3backend.UserGrantRole.wp_stepX EtcdGrove.apply.applierV3backend.wp_newHeader)

theorem apply_RoleGrantPermission_fuelX :
    EtcdGrove.apply.applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.RoleGrantPermission.wp_fuelX
    (EtcdGrove.apply.applierV3backend.RoleGrantPermission.wp_stepX EtcdGrove.apply.applierV3backend.wp_newHeader)

theorem apply_AuthEnable_fuelX :
    EtcdGrove.apply.applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG) :=
  EtcdGrove.apply.applierV3backend.AuthEnable.wp_fuelX
    (EtcdGrove.apply.applierV3backend.AuthEnable.wp_stepX EtcdGrove.apply.applierV3backend.wp_newHeader)

/-- **The backend applier's admin triples carrying the history's resource `X`** (the auth plan's
E2v, `apply/AdminChain.lean`): the authority with its fuel and `X` (the tie, `auth.tieRes`, for
the real store) through the five `SetUp` admin requests. -/
theorem apply_admin_backendX (E : EtcdGrove.apply.AEnv GF) (X : List auth.AuthState → IProp GF)
    (W : IProp GF) (p : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      EtcdGrove.apply.backendIs E p ∗ EtcdGrove.apply.backendAuthStepsX E p X W ⊢
      EtcdGrove.apply.applierAdmin E .backend
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) W
        (fun γa h => iprop(auth.authOwnFu γa h ∗ X h)) :=
  EtcdGrove.apply.applierAdmin_backendX apply_UserAdd_fuelX apply_RoleAdd_fuelX apply_UserGrantRole_fuelX
    apply_RoleGrantPermission_fuelX apply_AuthEnable_fuelX E X W p

end latestApply

#print axioms Perennial.EtcdGrove.apply_auth_steps_tie
#print axioms Perennial.EtcdGrove.apply_admin_backendX
#print axioms Perennial.EtcdGrove.auth_admin_permitted_latest
#print axioms Perennial.EtcdGrove.apply_auth_store_latest
#print axioms Perennial.EtcdGrove.apply_range_latest
#print axioms Perennial.EtcdGrove.apply_delete_range_latest
#print axioms Perennial.EtcdGrove.apply_put_latest
#print axioms Perennial.EtcdGrove.apply_txn_latest
#print axioms Perennial.EtcdGrove.auth_auth_enable_tie
#print axioms Perennial.EtcdGrove.auth_auth_disable_tie
#print axioms Perennial.EtcdGrove.auth_user_add_tie
#print axioms Perennial.EtcdGrove.auth_user_delete_tie
#print axioms Perennial.EtcdGrove.auth_user_change_password_tie
#print axioms Perennial.EtcdGrove.auth_user_grant_role_tie
#print axioms Perennial.EtcdGrove.auth_user_revoke_role_tie
#print axioms Perennial.EtcdGrove.auth_role_add_tie
#print axioms Perennial.EtcdGrove.auth_role_delete_tie
#print axioms Perennial.EtcdGrove.auth_role_grant_permission_tie
#print axioms Perennial.EtcdGrove.auth_role_revoke_permission_tie

section userAddSure
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`UserAdd` of a request whose password choice cannot fail** (the auth plan's E2u,
`auth/authStore__UserAdd_sure.lean`): no `ErrNoPasswordUser`, the outcome the step's alone, every
callee linked (`selectPassword`'s boundary says a base64 encoding decodes without an error). -/
theorem auth_user_add_sure :
    auth.authStore.UserAdd.specSure (GF := GF) (hG := hG) :=
  auth.authStore.UserAdd.wp_sure auth.authStore.wp_commitRevision
    auth.authStore.wp_refreshRangePermCache auth.authStore.wp_selectPassword zap.wp_String
    zap.Logger.wp_Info

end userAddSure

#print axioms Perennial.EtcdGrove.auth_user_add_sure

section kvLatest
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`UserAdd` keeping the tie, of a request whose password choice cannot fail** (the auth plan's
E2y, `auth/authStore__UserAdd_tieSure.lean`): E2s's `specT` and E2u's `specSure` in one triple,
every callee linked. -/
theorem auth_user_add_tie_sure :
    auth.authStore.UserAdd.specTSure (GF := GF) (hG := hG) :=
  auth.authStore.UserAdd.wp_tieSure auth.authStore.wp_commitRevision
    auth.authStore.wp_refreshRangePermCache auth.authStore.wp_selectPassword zap.wp_String
    zap.Logger.wp_Info

/-- **The auth applier's KV triples at the latest state** (the auth plan's E2y,
`apply/DispatchKVL.lean`): `applierKVL` of the auth applier, from its methods' latest-state
specs, over its store at the latest state and the lessor finding no lease. -/
theorem apply_applier_kv_latest (E : EtcdGrove.apply.AEnv GF) (ci : EtcdGrove.apply.Chain)
    (inner : GoInterface) (p : Loc) (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      EtcdGrove.apply.authIs E p inner ∗ EtcdGrove.apply.authIsL E p L ∗
      EtcdGrove.apply.lessorNil p ∗ EtcdGrove.apply.applierSpec E ci inner ⊢
      EtcdGrove.apply.applierKVL E (.auth E.authOn ci) ci
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3.ty) #p) L :=
  EtcdGrove.apply.applierKVL_auth apply_range_latest apply_delete_range_latest apply_put_latest
    apply_txn_latest E ci inner p L

/-- **The server's uber-applier's KV triples at the latest state, from its construction** (the
auth plan's E3k, `UberOn.lean`), every callee linked: over the server's store at the latest state
(`srvStoreLatest`) and its lessor finding no lease (`srvLessorNil`, a named premise). -/
theorem server_uber_kvl (s : Loc) (ua : GoInterface) (E : EtcdGrove.apply.AEnv GF)
    (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      srvUberBase s ua E ∗ srvStoreLatest s E L ∗ srvLessorNil s ⊢
      EtcdGrove.apply.uberKVL ua E (.quota .backend) L :=
  srv_uberKVL apply_range_latest apply_delete_range_latest apply_put_latest apply_txn_latest s ua E L

/-- **The same with auth on, the store's fact from the construction** (the auth plan's E3l,
`UberOn.lean`): `srvStoreLatest` discharged by the built part's store fact (of the store's
invariant), at the family `auth.latestRes stl` of the store the server's `authStore` field holds;
the lessor finding no lease stays a named premise. -/
theorem server_uber_kvl_on (s : Loc) (ua : GoInterface) (E : EtcdGrove.apply.AEnv GF)
    (γa : auth.AuthNames) (hM : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      srvUberBase s ua E ∗ srvLessorNil s ⊢
      ∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl ∗
        EtcdGrove.apply.uberKVL ua E (.quota .backend) (auth.latestRes stl (.on γa)) :=
  srv_uberKVL_on apply_range_latest apply_delete_range_latest apply_put_latest apply_txn_latest
    s ua E γa hM

/-- **`dispatch` on a KV request, the verdict at the latest state** (the auth plan's E2y,
`apply/DispatchKVL.lean`), every callee linked. -/
theorem apply_dispatch_kv_latest :
    EtcdGrove.apply.uberApplier.dispatch.kvSpecL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.uberApplier.dispatch.wp_kvL Perennial.EtcdGrove.apply.errors.wp_Is
    Perennial.EtcdGrove.txn.wp_ApplySecObserve Perennial.EtcdGrove.apply.txn.wp_WarnOfExpensiveRequest
    Perennial.EtcdGrove.apply.txn.wp_WarnOfFailedRequest

/-- **The uber-applier's `Apply` on a KV request with no alarm set, the verdict at the latest state
for the request's principal** (the auth plan's E2y, `apply/ApplyKVL.lean`). -/
theorem apply_uber_apply_kv_latest :
    EtcdGrove.apply.uberApplier.Apply.kvSpecL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.uberApplier.Apply.wp_kvL apply_dispatch_kv_latest

/-- **`apply.Apply` on a KV entry with no alarm set, the verdict at the latest state for the
request's principal** (the auth plan's E2y, `apply/ApplyFnKVL.lean`): the hypothesis of
`kv_applied_out_on` through `outcomeOn_of_kvOutL`. -/
theorem apply_apply_kv_latest :
    EtcdGrove.apply.Apply.kvSpecL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.Apply.wp_kvL Perennial.EtcdGrove.apply.pbutil.wp_MustUnmarshalMessage
    Perennial.EtcdGrove.apply.zap.wp_Stringer Perennial.EtcdGrove.apply.zap.Logger.wp_Debug
    Perennial.EtcdGrove.apply.wp_noSideEffect apply_uber_apply_kv_latest

end kvLatest

/-- **The apply thread's KV outcome is the mode-`on` model's** (the auth plan's E2v/E2y,
`KVOutcomeOn.lean`): the dispatched verdict at the latest state (`kvOutL`, `apply_apply_kv_latest`)
gives E2t's `outcomeOn`, for a plain KV request at the start chain with auth on and no alarm,
without `"\x00"` range ends (a transaction's verdict on its own permissions a theorem since E3e,
`txnVerdictOwn_of`). -/
theorem kv_outcome_on_latest [ext : FfiSyntax] (c₀ : w64) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (rq : EtcdGrove.apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : EtcdGrove.apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hna : EtcdGrove.apply.needAdminPermission rq = false)
    (hk : EtcdGrove.apply.isKVKind (EtcdGrove.apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (oc : EtcdGrove.apply.Outcome)
    (h : EtcdGrove.apply.kvOutL (.on γa) hs (auth.authInfoM (EtcdGrove.apply.principalOf rq))
      (.quota .backend) rq s.2 oc) :
    outcomeOn c₀ (EtcdGrove.apply.alarmChain true false false) s m (s.1, oc.logAfter s.2) :=
  outcomeOn_of_kvOutL c₀ s m rq ht hd hdec hv hna hk hp γa hs hl hz oc h

#print axioms Perennial.EtcdGrove.auth_user_add_tie_sure
#print axioms Perennial.EtcdGrove.apply_applier_kv_latest
#print axioms Perennial.EtcdGrove.apply_dispatch_kv_latest
#print axioms Perennial.EtcdGrove.apply_uber_apply_kv_latest
#print axioms Perennial.EtcdGrove.apply_apply_kv_latest
#print axioms Perennial.EtcdGrove.kv_outcome_on_latest

section adminLatest
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The auth applier's `Apply` with the admin check at the latest state** (the auth plan's E3c,
`apply/ApplyAdminL.lean`), every callee linked. -/
theorem apply_auth_apply_latest :
    EtcdGrove.apply.authApplierV3.Apply.specL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.authApplierV3.Apply.wp_latest Perennial.EtcdGrove.apply.wp_needAdminPermission

/-- **The base chain's inner applier does not reject** (the auth plan's E3c): the quota applier
over the backend. -/
theorem apply_apply_nr_base (pq pb : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3 go!"applierV3" pq ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #pb : GoInterface) ⊢
      EtcdGrove.apply.applyNR (.quota .backend)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3.ty) #pq) :=
  EtcdGrove.apply.applyNR_base Perennial.EtcdGrove.apply.applierV3backend.wp_Apply pq pb

/-- **The auth applier's latest-state `Apply` as an applier fact** (the auth plan's E3c). -/
theorem apply_applier_admin_latest (E : EtcdGrove.apply.AEnv GF) (c : EtcdGrove.apply.Chain)
    (inner : GoInterface) (p : Loc) (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      EtcdGrove.apply.authIs E p inner ∗ EtcdGrove.apply.authIsL E p L ∗
      EtcdGrove.apply.applyNR c inner ⊢
      EtcdGrove.apply.applierAdmL E (.auth E.authOn c)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3.ty) #p) L :=
  EtcdGrove.apply.applierAdmL_auth apply_auth_apply_latest E c inner p L

/-- **`dispatch` on an admitted admin request** (the auth plan's E2n, `apply/DispatchAdmin.lean`),
every callee linked. -/
theorem apply_dispatch_admin :
    EtcdGrove.apply.uberApplier.dispatch.adminSpec (GF := GF) (hG := hG) :=
  EtcdGrove.apply.uberApplier.dispatch.wp_admin Perennial.EtcdGrove.apply.errors.wp_Is
    Perennial.EtcdGrove.txn.wp_ApplySecObserve Perennial.EtcdGrove.apply.txn.wp_WarnOfExpensiveRequest
    Perennial.EtcdGrove.apply.txn.wp_WarnOfFailedRequest

/-- **The uber-applier's `Apply` on an admitted admin request with no alarm set, the admin check at
the latest state** (the auth plan's E3c, `apply/ApplyAdminL.lean`). -/
theorem apply_uber_apply_admin_latest :
    EtcdGrove.apply.uberApplier.Apply.adminSpecL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.uberApplier.Apply.wp_adminL apply_dispatch_admin

/-- **`apply.Apply` on an admitted admin entry with no alarm set, the admin check at the latest
state** (the auth plan's E3c, `apply/ApplyFnAdminL.lean`): a rejected entry's check refused at the
latest state (`adminStateR_of_rejL`), a dispatched one's passed (`adminOk_of_passL`). -/
theorem apply_apply_admin_latest :
    EtcdGrove.apply.Apply.adminSpecL (GF := GF) (hG := hG) :=
  EtcdGrove.apply.Apply.wp_adminL Perennial.EtcdGrove.apply.pbutil.wp_MustUnmarshalMessage
    Perennial.EtcdGrove.apply.zap.wp_Stringer Perennial.EtcdGrove.apply.zap.Logger.wp_Debug
    Perennial.EtcdGrove.apply.wp_noSideEffect apply_uber_apply_admin_latest

end adminLatest

/-- **A refused admin check keeps the model's auth state; a passed one admits the principal** (the
auth plan's E3c, `ApplyTieOn.lean`): `adminStateR`'s two cases from the latest-state verdicts. -/
theorem admin_state_of_latest [ext : FfiSyntax] (γa : auth.AuthNames) (hs : List auth.AuthState)
    (st : auth.AuthState) (rq : EtcdGrove.apply.IRRModel) (hl : hs.getLast? = some st) :
    (EtcdGrove.apply.adminRejL (.on γa) hs rq → adminStateR rq st st) ∧
      (EtcdGrove.apply.needAdminPermission rq = true → EtcdGrove.apply.adminPassL (.on γa) hs rq →
        auth.adminOk st (some (auth.authInfoM (EtcdGrove.apply.principalOf rq)))) :=
  ⟨adminStateR_of_rejL γa hs st rq hl, adminOk_of_passL γa hs st rq hl⟩

/-- **`AuthEnable`'s result is the model's step at the latest state's flag** (the auth plan's E3c,
`ApplyTieOn.lean`): `AdminReq.result`'s relation `authEnableR` in the mode `on`. -/
theorem admin_state_auth_enable [ext : FfiSyntax] (γa : auth.AuthNames) (rq : EtcdGrove.apply.IRRModel)
    (st : auth.AuthState) (en : Bool) (o : auth.Outcome)
    (ha : auth.adminOk st (some (auth.authInfoM (EtcdGrove.apply.principalOf rq))))
    (hk : EtcdGrove.apply.dispatchKind rq = .authEnable) (h : EtcdGrove.apply.authEnableR (.on γa) en st o) :
    adminStateR rq st (outState st o) :=
  adminStateR_of_authEnable γa rq st en o ha hk h

#print axioms Perennial.EtcdGrove.apply_auth_apply_latest
#print axioms Perennial.EtcdGrove.admin_state_auth_enable
#print axioms Perennial.EtcdGrove.apply_apply_nr_base
#print axioms Perennial.EtcdGrove.apply_applier_admin_latest
#print axioms Perennial.EtcdGrove.apply_dispatch_admin
#print axioms Perennial.EtcdGrove.apply_uber_apply_admin_latest
#print axioms Perennial.EtcdGrove.apply_apply_admin_latest
#print axioms Perennial.EtcdGrove.admin_state_of_latest

section userAddHandler
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's `UserAdd` proposes a request whose password choice cannot fail** (the auth
plan's E2x, `EtcdServer__UserAdd.lean`): unless no password is asked for, the password is hashed
(`bcrypt.GenerateFromPassword`, the trust boundary, D-AU6) and its hash put base64-encoded
(`StdEncoding.EncodeToString`, base64's package fact) with the password cleared, so the proposed
model is `pwSure`: the proposer's obligation of E2t/E2u, discharged at the handler. -/
theorem server_user_add_sure :
    EtcdServer.UserAdd.spec (GF := GF) (hG := hG) :=
  EtcdServer.wp_UserAdd

end userAddHandler

#print axioms Perennial.EtcdGrove.server_user_add_sure

section tokens
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The simple token provider's constructor** (`newTokenProviderSimple`, the auth plan's S5e;
`auth/TokenKeeperRun.lean`): the provider's facts, its index waiter, the admin side's share and the
authority over the rights to issue tokens, under fresh names. -/
theorem token_simple_new (lg : Loc) (iw : GoFunc) (ttl : time.Duration) (hpos : 0 < sint.Z ttl) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
        □ (∀ idx : w64, {{ True }} (App (Val #iw) (Val #idx)) {{ (ch : Loc), RET #ch; auth.anyRecv ch }}) }}
      (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.newTokenProviderSimple)) (Val #lg)) (Val #iw))
        (Val #ttl))
    {{ (p : Loc), RET #p; ∃ γt γf : GName, auth.simpleOk p γt γf ∗ auth.simpleWaitOk p ∗
        auth.simpleAdmin p ∗ ghostMapAuth γf 1 (∅ : GMap GoString Unit) }} :=
  auth.tokenSimple_new zap.NewNop.wp_proof lg iw ttl hpos

/-- **The simple token provider meets the token contract** with `info`'s context premise
(`auth.tokenProviderOkCtx`, S5e), in the mode `on γa`, with the admin side's share, and no
hypothesis on the provider (the keeper's goroutine proved, `keeper_run`). -/
theorem token_simple_ok (p : Loc) (γa : auth.AuthNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.simpleOk p γa.tok γa.fresh ∗
        auth.simpleWaitOk p ⊢
      auth.tokenProviderOkCtx (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty) #p)
        (.on γa) (auth.simpleAdmin p) :=
  auth.tokenSimple_okCtx zap.Logger.Debug.wp_proof zap.String.wp_proof p γa

/-- **The auth store's constructor in the mode `on γa`** (`NewAuthStore`, the auth plan's E2a;
`auth/NewAuthStoreOn.lean`): over the store's backend contracts and the token provider's, the
store's invariant, the admin side's write resource, the provider's share, the authority (the
first revision committed if the backend's state had none) and the readers' slots. -/
theorem auth_store_new_on (lg : Loc) (ab tp : GoInterface) (cost : w64) (bi : GoInterfaceOk)
    (γa : auth.AuthNames) (R P : IProp GF) (f : val) (T A Pre Q Post : IProp GF)
    (hs : List auth.AuthState) (stl : auth.AuthState) (hlast : hs.getLast? = some stl)
    (hfit : auth.permsFit stl) (hempty : ∃ s ∈ hs, s.users = ∅) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
        ⌜ab = GoInterface.ok bi⌝ ∗ auth.authBackendOk ab R (.on γa) ∗
        auth.authWBackendOkR ab (.on γa) P f T ∗
        □ ({{ T }} (App (Val #(methods bi.ty go!"CreateAuthBuckets" bi.v)) (Val #()))
          {{ RET #(); T }}) ∗
        T ∗ mvcc.csContract P f Pre Q Post ∗ auth.tokenProviderOkA tp (.on γa) A ∗ A ∗
        auth.authOwn (.on γa) hs ∗ auth.authStoreInit γa stl }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
        (Val #ab)) (Val #tp)) (Val #cost))
    {{ (st : GoInterface), RET #st; ∃ (stp : Loc) (hs' : List auth.AuthState),
        ⌜st = auth.authIface stp⌝ ∗ auth.authInv stp R (.on γa) ∗
        auth.authWRAt stp (.on γa) P f T ab ∗
        auth.tpAdmin stp (.on γa) ∗ Post ∗ auth.authOwn (.on γa) hs' ∗
        ⌜(stl.revision ≠ 0 ∧ hs' = hs) ∨ (stl.revision = 0 ∧ hs' = hs ++ [auth.bump stl])⌝ ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          auth.enabledRd stp (.on γa) ∗ auth.cacheRd stp (.on γa) ∗ auth.beRd stp R (.on γa)) }} :=
  auth.newAuthStore_on zap.Logger.wp_Warn zap.Int'.wp_proof auth.authStore.wp_Revision
    auth.authStore.wp_commitRevision auth.authStore.wp_setupMetricsReporter
    auth.authStore.wp_refreshRangePermCache lg ab tp cost bi γa R P f T A Pre Q Post hs stl hlast
    hfit hempty

/-- **`NewAuthStore` at the server's boot, in the mode `on γa`** (the auth plan's E2e;
`auth.newAuthStore_boot`, `Proof/go_etcd_io/etcd/server/v3/auth/Boot.lean`): the auth names
allocated over the boot state with the token provider's names, the batch lock's half of the history
handed to the backend, whose contracts for the new names are the named premise D22 discharges
(`auth.authSchemaBoot`); the store's invariant, the admin side's write resource, the provider's
share and the admin side's authority at `[bootState, bump bootState]`. -/
theorem auth_store_boot_on (lg : Loc) (ab tp : GoInterface) (cost : w64) (bi : GoInterfaceOk)
    (γt γf : GName) (R P : IProp GF) (f : val) (T A Pre Q Post : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
        ⌜ab = GoInterface.ok bi⌝ ∗ auth.authSchemaBoot ab bi γt γf R P f T ∗
        T ∗ mvcc.csContract P f Pre Q Post ∗ auth.tokenProviderBoot tp γt γf A ∗ A }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
        (Val #ab)) (Val #tp)) (Val #cost))
    {{ (st : GoInterface), RET #st; ∃ (γa : auth.AuthNames) (stp : Loc),
        ⌜γa.tok = γt ∧ γa.fresh = γf⌝ ∗ ⌜st = auth.authIface stp⌝ ∗ auth.authInv stp R (.on γa) ∗
        auth.authWR stp (.on γa) P f T ∗ auth.tpAdmin stp (.on γa) ∗ Post ∗
        auth.authOwn (.on γa) [auth.bootState, auth.bump auth.bootState] ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          auth.enabledRd stp (.on γa) ∗ auth.cacheRd stp (.on γa) ∗ auth.beRd stp R (.on γa)) }} :=
  auth.newAuthStore_boot zap.Logger.wp_Warn zap.Int'.wp_proof auth.authStore.wp_Revision
    auth.authStore.wp_commitRevision auth.authStore.wp_setupMetricsReporter
    auth.authStore.wp_refreshRangePermCache lg ab tp cost bi γt γf R P f T A Pre Q Post

/-- **The server's bound request side, of the real store** (the auth plan's E2e;
`srvAuthBound_of_authInv`, `AuthBound.lean`): `srvAuthBound` from the store's invariant in the
server's mode, the guards' bound variants' premise. -/
theorem srv_auth_bound_of_inv (s stp : Loc) (R : IProp GF) (E : apply.AEnv GF)
    (hRD : E.RD = auth.authRd stp R E.authMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ auth.authIface stp ∗
      auth.authInv stp R E.authMode ⊢ srvAuthBound s E :=
  srvAuthBound_of_authInv auth.authStore.wp_AuthInfoFromCtx s stp R E hRD

end tokens

#print axioms Perennial.EtcdGrove.token_simple_new
#print axioms Perennial.EtcdGrove.token_simple_ok
#print axioms Perennial.EtcdGrove.auth_store_new_on
#print axioms Perennial.EtcdGrove.auth_store_boot_on
#print axioms Perennial.EtcdGrove.srv_auth_bound_of_inv

section serverAuth
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's token provider and auth store with auth on** (the auth plan's E2i;
`authSrvTP_on`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthSrv.lean`): `NewTokenProvider`
with the simple provider gives the auth names allocated over the boot state and `NewAuthStore`'s
construction in the mode `on γa` (`authStoreKit`): the store from its proofs, not
`NewAuthStore`'s axiom, its request side and apply contract of its invariant (its admin clauses
vacuous: `apply.adminAdmitted`). Its named premises: D22's part (`authSchemaSrv`) and
`isValidSimpleToken`'s spec for any context (`auth.ValidSpec`). What `NewServer`'s proof will take
with auth on (`notes/decisions.md`, "E2i of the auth plan"). -/
theorem srv_auth_tp_on (hValid : auth.ValidSpec (GF := GF) (hG := hG))
    (hD22 : ⊢ authSchemaSrv (GF := GF)) : authSrvTP (GF := GF) (hG := hG) true :=
  authSrvTP_on auth.wp_NewTokenProvider hValid zap.Logger.wp_Debug zap.String.wp_proof
    zap.Logger.wp_Warn zap.Int'.wp_proof auth.authStore.wp_Revision auth.authStore.wp_commitRevision
    auth.authStore.wp_setupMetricsReporter auth.authStore.wp_refreshRangePermCache
    auth.authStore.wp_AuthInfoFromCtx auth.authStore.wp_AuthInfoFromTLS
    auth.authStore.wp_IsPutPermitted auth.authStore.wp_IsRangePermitted
    auth.authStore.wp_IsDeleteRangePermitted auth.authStore.wp_IsAdminPermitted
    auth.authStore.wp_IsAuthEnabled auth_put_permitted_latest auth_range_permitted_latest
    auth_delete_range_permitted_latest auth_admin_permitted_latest
    (auth.authStore.AuthEnable.wp_tieB auth.authStore.wp_refreshRangePermCache
      auth.authStore.wp_setRevision auth.wp_hasRootRole zap.Logger.wp_Info)
    (auth.authStore.UserAdd.wp_tieSureB auth.authStore.wp_commitRevision
      auth.authStore.wp_refreshRangePermCache auth.authStore.wp_selectPassword zap.wp_String
      zap.Logger.wp_Info)
    (auth.authStore.RoleAdd.wp_tieB auth.authStore.wp_commitRevision zap.wp_String
      zap.Logger.wp_Info)
    (auth.authStore.UserGrantRole.wp_tieB auth.authStore.wp_commitRevision
      auth.authStore.wp_refreshRangePermCache zap.wp_String zap.wp_Strings zap.Logger.wp_Warn
      zap.Logger.wp_Info)
    (auth.authStore.RoleGrantPermission.wp_tieB auth.authStore.wp_commitRevision
      auth.authStore.wp_refreshRangePermCache auth.wp_isValidPermissionRange zap.wp_String
      zap.wp_ByteString zap.Logger.wp_Info) hD22

/-- **The same with auth off** (`authSrvTP_off`): of `NewTokenProvider`'s proof and
`NewAuthStore`'s axiom, what `NewServer`'s proof takes today. -/
theorem srv_auth_tp_off : authSrvTP (GF := GF) (hG := hG) false :=
  authSrvTP_off auth.wp_NewTokenProvider auth.wp_NewAuthStore

/-- **`NewServer` with auth on** (the auth plan's E2k): `NewServer.specM true`, the server started with
the simple token provider and the auth store of `srv_auth_tp_on` (its proofs, not `NewAuthStore`'s
axiom), the apply environment's auth on, the start's chain with the auth layer enabled; every callee
linked as in `wp_NewServer` (`NewServer.wp_proofM`, whose mode off gives `wp_NewServer`'s
statement). Its named premises are `srv_auth_tp_on`'s: D22's part (`authSchemaSrv`) and
`isValidSimpleToken`'s spec for any context (`auth.ValidSpec`). Since E2w (2026-10-26) its KV
invariant is the mode's (`kvInvM true`, `kvInvOn`), allocatable at the bootstrap log
(`kvInvOn_alloc_boot`), and its post the mode-indexed built part (`srvBuiltG true`): until then it
took `kvInv`, whose start chain is mode-`off`, so its precondition was unsatisfiable
(`kvInv_ch0_on_false`, E2p). -/
theorem server_new_auth_on [go_etcd_io.etcd.cache.v3.Assumptions] [MemStorReg GF]
    [EtcdGrove.Float64ToInt64Semantics] [EtcdGrove.ErrorStringLeaf]
    (hValid : auth.ValidSpec (GF := GF) (hG := hG))
    (hD22 : ⊢ authSchemaSrv (GF := GF)) : NewServer.specM (GF := GF) (hG := hG) true :=
  NewServer.wp_proofM true zap.Logger.wp_Error zap.wp_Error zap.Logger.wp_Info zap.Logger.wp_Warn
    v2stats.wp_NewServerStats membership.RaftCluster.wp_String v2stats.wp_NewLeaderStats
    types.ID.wp_String_ptr bootstrappedRaft.wp_newRaftNode node.wp_Ready node.wp_Advance
    node.wp_Tick node.wp_ReadIndex types.URLs.wp_StringSlice idutil.wp_NewGenerator
    notify.wp_NewNotifier wp_addFeatureGateMetrics prometheus.GaugeVec.wp_With
    membership.RaftCluster.wp_SetVersionChangedNotifier EtcdServer.wp_Logger
    config.ServerConfig.wp_ReqTimeout EtcdServer.wp_FeatureEnabled time.Duration.wp_Seconds_ptr
    math.wp_Ceil lease.wp_NewLessor (srv_auth_tp_on hValid hD22) mvcc.wp_New wp_newCorruptionChecker
    mvcc.store.wp_HashStorage schema.wp_NewAuthBackend v3compactor.wp_New
    EtcdServer.wp_restoreAlarms EtcdServer.wp_NewUberApplier
    EtcdServer.wp_getTxPostLockInsideApplyHook backend.backend.wp_SetTxPostLockInsideApplyHook
    config.ServerConfig.wp_PeerDialTimeout membership.RaftCluster.wp_ID rafthttp.Transport.wp_Start
    rafthttp.Transport.wp_AddRemote rafthttp.Transport.wp_AddPeer mvcc.watchableStore.wp_Close
    schema.bucket.wp_ID schema.bucket.wp_Name schema.bucket.wp_IsSafeRangeBucket
    lease.lessor.wp_GetLease lease.lessor.wp_Attach lease.lessor.wp_Detach
    lease.lessor.wp_SetRangeDeleter lease.lessor.wp_Lookup lease.lessor.wp_Grant
    lease.lessor.wp_Checkpoint lease.Lease.wp_TTL lease.lessor.wp_Promote lease.lessor.wp_Demote
    lease.lessor.wp_ExpiredLeasesC backend.backend.wp_ConcurrentReadTx backend.backend.wp_ReadTx
    backend.backend.wp_BatchTx backend.backend.wp_ForceCommit backend.backend.wp_Size
    backend.backend.wp_SizeInUse backend.concurrentReadTx.wp_RLock
    backend.concurrentReadTx.wp_RUnlock backend.concurrentReadTx.wp_UnsafeRange
    backend.readTx.wp_RLock backend.readTx.wp_RUnlock backend.readTx.wp_UnsafeRange
    backend.batchTxBuffered.wp_LockInsideApply backend.batchTxBuffered.wp_LockOutsideApply
    backend.batchTxBuffered.wp_UnsafeSeqPut backend.batchTxBuffered.wp_Unlock
    backend.batchTxBuffered.wp_UnsafeRange backend.batchTxBuffered.wp_UnsafeCreateBucket
    node.wp_Propose EtcdServer.wp_MemberID EtcdServer.wp_Leader EtcdServer.wp_Term
    EtcdServer.wp_ForceSnapshot consistentIndex.wp_ConsistentIndex EtcdServer.wp_ClusterVersion
    MemoryStorage.wp_Snapshot node.wp_ApplyConfChange node.wp_Step node.wp_ReportUnreachable
    node.wp_ReportSnapshot EtcdServer.wp_Process EtcdServer.wp_IsIDRemoved
    EtcdServer.wp_ReportUnreachable EtcdServer.wp_ReportSnapshot
    backend.batchTxBuffered.wp_UnsafeDelete

end serverAuth

#print axioms Perennial.EtcdGrove.srv_auth_tp_on
#print axioms Perennial.EtcdGrove.srv_auth_tp_off
#print axioms Perennial.EtcdGrove.server_new_auth_on

section serverAuthAlloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A new cluster's resources with auth on** (the auth plan's E2z, `NewServerAllocOn.lean`):
`srvClusterBoot_alloc`'s, with the mode-`on` KV invariant `kvInvOn _ _ srvAuthSt0` at the start
chain with auth on; with `server_member_alloc_on`, what `server_new_auth_on`'s caller allocates. -/
theorem server_cluster_alloc_on (cfg nodes : GSet w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (Hcne : cfg ≠ ∅) (Hnz : W64 0 ∉ nodes) (Hcfg : cfg = GMap.listToSet ps)
    (hboot : BootLogOk ccOk ps bootLog)
    (hpol : ∀ ty d, ccOk ty d →
      ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk cfg d)
    (Hpd : (ps.map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hp0 : ∀ id ∈ ps, uint.Z id % 2 ^ 16 ≠ 0) :
    ⊢ |={⊤}=> ∃ (γ : RaftNames) (issued cnt : GName) (γk : KVNames),
        ⌜γ.reCfg = cfg ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk ∧ γ.reBoot = bootLog ∧
          γ.reNoSnap = true ∧ γ.reNoXfer = true ∧
          γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain true false false ∧ γk.log0 = [[], []] ∧
          γk.ids.issued = issued⌝ ∗
        raftCommitInv (GF := GF) γ ∗ isCommitted γ bootLog ∗ rdCredInv γ ∗
        ([∗map] id ↦ _u ∈ toMap nodes, ownRaftGhost γ id (bootPState bootLog)) ∗
        kvInvOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 ∗
        etcdKV γk (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries bootLog))) ∗
        idClusterInv issued cnt Φs ∗ (W64 0) ↪[issued]□ (none : Option (List w8 × GName)) ∗
        srvPropMint ⟨γ, [], W64 0⟩ γk.ids ∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued ∗
        ([∗list] id ∈ ps, (idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) ∗
          rdCred γ (2 ^ 48) ∗
          ∃ γd : GName, ⌜γ.reSnapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))) ∗
        [∗list] id ∈ ps, idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) :=
  srvClusterBootOn_alloc cfg nodes ccOk ps bootLog Φs Hcne Hnz Hcfg hboot hpol Hpd Hp0

/-- **A member's names with auth on** (`srvMemberBootOn_alloc`): the mode-`on` KV invariant at
its names, as `NewServer.specM true`'s `kvInvM true`. -/
theorem server_member_alloc_on (γ : RaftNames) (cnt : GName) (γk : KVNames) (id : w64)
    (cok : GName) :
    ⊢ kvInvOn (GF := GF) ⟨γ, [], W64 0⟩ γk srvAuthSt0 -∗
      idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) -∗
      idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) ==∗
      ∃ ρ : ReqNames,
        ⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧
          ρ.rd.kv.ch0 = γk.ch0 ∧ ρ.rd.kv.log0 = γk.log0 ∧
          ρ.rd.kv.cok = cok ∧ ρ.ids.issued = γk.ids.issued ∧ ρ.ids.cnt = cnt ∧
          ρ.ids.pfx = idPfxOf (W16 (uint.Z id))⌝ ∗
        kvInvM true ⟨γ, [], W64 0⟩ ρ.rd.kv srvAuthSt0 ∗ idShare ρ.ids ∗
        srvReadNamesFreshNK ρ.rd ∗ idWaitTok ρ.ids :=
  srvMemberBootOn_alloc γ cnt γk id cok

/-- **`start`'s construction premise in the auth mode, from `NewServer.specM`'s built part**
(`isServerBuilt_of_gapM`, E2z): `isServerBuilt` with auth off, `isServerBuiltOn` (the mode-`on`
rows, the apply thread's KV ghost state over the mode-`on` model) with auth on. -/
theorem server_built_gap_on (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF)
    (γn : RNNames) (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    srvBuiltG on s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ N ∗ srvBuildGap s γn ai₀ at₀ ⊢
      isServerBuiltM on s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N :=
  isServerBuilt_of_gapM on s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N

end serverAuthAlloc

#print axioms Perennial.EtcdGrove.server_cluster_alloc_on
#print axioms Perennial.EtcdGrove.server_member_alloc_on
#print axioms Perennial.EtcdGrove.server_built_gap_on

section goroutines
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's apply loop** (`run`, the request path's unit 4c; `Spec/go_etcd_io/etcd/server/
v3/etcdserver/EtcdServer__run.lean`): from `isServerRun` (`start`'s), it applies every batch raft
commits through the FIFO scheduler, the apply thread's resources chained from job to job, and
shuts down. -/
theorem server_run [ErrorStringLeaf] : EtcdServer.run.spec (GF := GF) (hG := hG) := EtcdServer.wp_run

/-- **The server's `start`** (the request path's unit 4c; `Spec/.../EtcdServer__start.lean`): from
the construction premise `isServerBuilt` alone, the server's views and `run` started. -/
theorem server_start [ErrorStringLeaf] : EtcdServer.start.spec (GF := GF) (hG := hG) := EtcdServer.wp_start

/-- **The server's `Start`** (the request path's unit 4c; `Spec/.../EtcdServer__Start.lean`):
`start`, then the read loop and nine names-only monitors through `GoAttach`. -/
theorem server_Start [ErrorStringLeaf] : EtcdServer.Start.spec (GF := GF) (hG := hG) := EtcdServer.wp_Start

/-- **`start` gives the request path's views** (the request path's unit 4c): from the construction
premise, `start` returns the views `range_linearizable`, `txn_applied` and the v3rpc results take
(`isServerReq`, `isServerRead`), the read loop's `server` contract over them (`read_server`), and
the read loop's lock's reader slots (`srvRdCall`'s `srvReadReader`): those results are conditional
on `isServerBuilt` alone (and each call's own resources). -/
theorem start_gives_views [ErrorStringLeaf] (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat)
    (Hrb : receiptBound GF ≤ N + 1) (Hai0 : ai₀ = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"start")) (Val #()))
    {{ RET #(); ∃ γw : GName, isServerReq s E { ρ with wait := γw } ∗ isServerRead s E γr ∗
        isReadServer (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) γr (srvReadLR s)
          (idCred ρ.ids 1) ∗
        [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          srvReadReader s γr }} := by
  iintro %Φ ⟨#Hpkg, Hb⟩ HΦ
  iapply (server_start s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N Hrb Hai0) $$ [Hb]
  · iframe Hpkg Hb
  inext
  iintro ⟨%γw, #Hreq, #Hrd, Hst, -⟩
  iunfold srvStarted at Hst
  iNamed Hst
  ihave #Hrs := read_server s E { ρ with wait := γw } γr Hρrd $$ [$Hpkg $Hreq $Hrd]
  iapply HΦ
  iexists γw
  iframe Hreq Hrd Hrs Hrds

/-- **The FIFO scheduler's contract** (`schedule.Scheduler.Schedule`, the trust boundary; the request
path's unit 4c): a job scheduled with a tracked chain runs after every job scheduled before it on
the same scheduler, its `Prev` the previous job's `Post` (`schedPre`/`schedPost`, the queue of saved
postconditions); untracked, it runs with its own `Pre` while the scheduler is live. -/
theorem scheduler_fifo : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG) :=
  schedule.Scheduler.wp_Schedule

end goroutines

#print axioms Perennial.EtcdGrove.cindex_hook_backend
#print axioms Perennial.EtcdGrove.cindex_hookFnSpec
#print axioms Perennial.EtcdGrove.backend_server_hooks
#print axioms Perennial.EtcdGrove.server_kv_backend_hooks
#print axioms Perennial.EtcdGrove.applyEntries_model
#print axioms Perennial.EtcdGrove.applyAll_model
#print axioms Perennial.EtcdGrove.applied_log_at
#print axioms Perennial.EtcdGrove.read_server
#print axioms Perennial.EtcdGrove.read_raft
#print axioms Perennial.EtcdGrove.node_contract_ifc
#print axioms Perennial.EtcdGrove.node_contract_propose
#print axioms Perennial.EtcdGrove.node_contract_memstor
#print axioms Perennial.EtcdGrove.wait_time
#print axioms Perennial.EtcdGrove.applyEntries_trace
#print axioms Perennial.EtcdGrove.applyEntries_kv
#print axioms Perennial.EtcdGrove.applyEntries_replay_no_write
#print axioms Perennial.EtcdGrove.applyEntries_replay_all
#print axioms Perennial.EtcdGrove.applyEntries_rejected_no_write
#print axioms Perennial.EtcdGrove.EtcdServer.wp_apply
#print axioms Perennial.EtcdGrove.EtcdServer.wp_applyEntryNormal
#print axioms Perennial.EtcdGrove.request_handoff
#print axioms Perennial.EtcdGrove.request_delivered
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

section serverProposeOn
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The proposer's handoff in the auth mode `on`** (the auth plan's E3b, `ReqOn.lean`): the
result at the header the server stamps, the applied result's auth verdict the model's grant at the
committed prefix before the entry (`resPostM true`, `authTie`). Every callee linked. -/
theorem server_process_irr_on :
    EtcdServer.processInternalRaftRequestOnce.specM (GF := GF) (hG := hG) true :=
  EtcdServer.processInternalRaftRequestOnce.wp_proofM true EtcdServer.wp_getAppliedIndex
    EtcdServer.wp_getCommittedIndex EtcdServer.wp_FeatureEnabled wp_exceedsRequestLimit
    idutil.Generator.wp_Next EtcdServer.wp_AuthInfoFromCtx wp_getRequestType proto.wp_MarshalIRR
    config.ServerConfig.wp_ReqTimeout trace.wp_SpanFromContext
    (EtcdServer.parseProposeCtxErr.wp_proofM true errors.wp_IsCtxErr time.Time.wp_After
      EtcdServer.wp_getLead EtcdServer.wp_MemberID membership.RaftCluster.wp_Members
      wp_isConnectedToQuorumSince wp_isConnectedSince)
    context.wp_ErrDone strconv.wp_FormatBool time.Duration.wp_Seconds
    prometheus.HistogramVec.wp_WithLabelValues

/-- `raftRequest` in the auth mode `on`, every callee linked. -/
theorem server_raft_request_on :
    EtcdServer.raftRequest.specM (GF := GF) (hG := hG) true :=
  EtcdServer.raftRequest.wp_proofM true server_process_irr_on trace.wp_SpanFromContext
    context.wp_ValueStartTime traceutil.Trace.wp_GetStartTime traceutil.Trace.wp_SetStartTime
    traceutil.Trace.wp_InsertStep traceutil.Trace.wp_LogIfLong

/-- **A put in the auth mode `on`**: a success is a put the auth state its entry met granted, its
client's result at the log the entry met; a refusal an error. Every callee linked. -/
theorem server_put_on : EtcdServer.Put.specOn (GF := GF) (hG := hG) :=
  EtcdServer.Put.wp_proofOn server_raft_request_on PutRequest.wp_GetKey traceutil.Tracer.wp_Start
    trace.wp_WithAttributes «attribute».wp_String context.wp_WithValue

/-- **A delete in the auth mode `on`** (`server_put_on`'s). Every callee linked. -/
theorem server_delete_range_on : EtcdServer.DeleteRange.specOn (GF := GF) (hG := hG) :=
  EtcdServer.DeleteRange.wp_proofOn server_raft_request_on DeleteRangeRequest.wp_GetKey
    DeleteRangeRequest.wp_GetRangeEnd traceutil.Tracer.wp_Start trace.wp_WithAttributes
    «attribute».wp_String

/-- **A writing transaction in the auth mode `on`** (`server_put_on`'s; the auth plan's E3d): a
success is a transaction the auth state its entry met granted, its client's result at the log the
entry met; a refusal an error. Every callee linked. -/
theorem server_txn_on : EtcdServer.Txn.specOn (GF := GF) (hG := hG) :=
  EtcdServer.Txn.wp_proofOn txn.wp_IsTxnReadonly traceutil.Tracer.wp_Start trace.wp_WithAttributes
    TxnRequest.wp_GetCompare wp_firstCompareKey «attribute».wp_String TxnRequest.wp_GetSuccess
    wp_firstOpKey wp_firstOpType wp_firstOpLease «attribute».wp_Int64 «attribute».wp_Int
    TxnRequest.wp_GetFailure «attribute».wp_Bool EtcdServer.wp_Logger traceutil.wp_EnsureTrace
    context.wp_WithValue server_raft_request_on

end serverProposeOn

section applyEntryOn
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Before `apply.Apply` on a KV entry with auth on** (the auth plan's E3f, `ApplyEntryOn.lean`):
the model's state after the entry certified, and the certificates the latest-state triple asks. -/
theorem apply_kv_entry_pre_on (E : EtcdGrove.apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (m : EntryModel) (x : EtcdGrove.apply.ApplyKV) (st : auth.AuthState)
    (rq : EtcdGrove.apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : EtcdGrove.apply.irrDecode m.data = some rq) (hv : uint.Z γr.kv.c0 < uint.Z m.index)
    (hk : EtcdGrove.apply.isKVKind (EtcdGrove.apply.dispatchKind rq) = true)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some st)
    (hz : noZeroEnds rq)
    (hlen : (kvEntryOn γr.kv.c0 x.chain (st, x.log) m).2.length < 2 ^ 63) :
    ⊢ srvKVInvsOn (GF := GF) E γr st₀ -∗ kvAppliedOn γr.raft γr.kv st₀ A x st -∗
      srvRLogLb γr.raft (A ++ [m]) ={⊤}=∗
      ⌜plainCover rq ∧ EtcdGrove.apply.needAdminPermission rq = false ∧
        entryDetOn γr.kv.c0 (st, x.log) m ∧ x.chain = EtcdGrove.apply.alarmChain true false false⌝ ∗
      EtcdGrove.apply.certPreVW true E x.chain rq x.log
        (EtcdGrove.apply.kvOutL (.on γa) hs (auth.authInfoM (EtcdGrove.apply.principalOf rq))
          (.quota .backend) rq x.log) ∗
      kvAppliedLOn γr.raft γr.kv st₀ (A ++ [m]) (kvEntryOn γr.kv.c0 x.chain (st, x.log) m) :=
  kv_entry_pre_on E γr st₀ A m x st rq ht hd hdec hv hk γa hs hl hz hlen

/-- **After `apply.Apply` on a KV entry with auth on** (E3f): the apply thread's state is the
model's (`kvOn_after_kv`). -/
theorem apply_kv_after_on (c₀ : w64) (st : auth.AuthState) (x x' : EtcdGrove.apply.ApplyKV)
    (m : EntryModel) (rq : EtcdGrove.apply.IRRModel) (out : EtcdGrove.apply.ApplyOut)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : EtcdGrove.apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hna : EtcdGrove.apply.needAdminPermission rq = false)
    (hk : EtcdGrove.apply.isKVKind (EtcdGrove.apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some st)
    (hz : noZeroEnds rq)
    (hdet : entryDetOn c₀ (st, x.log) m) (hch : x.chain = EtcdGrove.apply.alarmChain true false false)
    (hstep : EtcdGrove.apply.applyStep rq true x x' out)
    (hout : ∀ o b, out = .dispatched o b →
      EtcdGrove.apply.kvOutL (.on γa) hs (auth.authInfoM (EtcdGrove.apply.principalOf rq))
        (.quota .backend) rq x.log o) :
    x'.chain = x.chain ∧ (st, x'.log) = kvEntryOn c₀ x.chain (st, x.log) m :=
  kvOn_after_kv c₀ st x x' m rq out ht hd hdec hv hna hk hp γa hs hl hz hdet hch hstep hout

end applyEntryOn

section applyStateOn
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The applied index's deposit in the auth mode** (the auth plan's E3i, `AppliedOn.lean`): the
apply thread deposits the log after the next entry, the mode's model of the committed raft log. -/
theorem server_applied_predeposit_on (on : Bool) (s : Loc) (E : EtcdGrove.apply.AEnv GF)
    (γr : ReadNames) (v v' : w64) (L₀ L : mvcc.Log) (hv : uint.Z v' = uint.Z v + 1)
    (hp : L₀ <+: L) :
    ⊢ srvAppliedInvM (GF := GF) on s E γr -∗ srvAppliedOwn γr v -∗ appliedLogAt γr v L₀ -∗
      kvLogAtM on γr v' L ={⊤}=∗ srvAppliedPre γr v v' L :=
  applied_predepositM on s E γr v v' L₀ L hv hp

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

/-- **`apply.Apply`'s result with auth on is not `ErrNoSpace`'s** (the auth plan's E3i,
`NoSpaceDeadOn.lean`): `applyEntryNormal`'s NOSPACE branch is dead for a covered entry at the
start's chain with auth on, the auth layer's refusal included. -/
theorem server_apply_not_nospace_on (rq : EtcdGrove.apply.IRRModel) (x x' : EtcdGrove.apply.ApplyKV)
    (ar : Loc) (out : EtcdGrove.apply.ApplyOut) (hp : plainCover rq)
    (hch : x.chain = EtcdGrove.apply.alarmChain true false false)
    (hs : EtcdGrove.apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      EtcdGrove.apply.applyResultIs rq true x.log ar out -∗
      EtcdGrove.apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) :=
  applyResultIs_notNoSpaceOn rq x x' ar out hp hch hs

/-- **`apply.Apply`'s result on an admitted admin entry with auth on is not `ErrNoSpace`'s** (the
auth plan's E3j, `NoSpaceDeadAdminOn.lean`): with `apply.Apply.adminSpecL`'s postcondition (the
admin outcome and the rejection's error), the result is `nil` or its error one of the auth
package's, so `applyEntryNormal`'s NOSPACE branch is dead for admin entries too. -/
theorem server_apply_admin_not_nospace_on
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (γa : auth.AuthNames)
    (M : auth.AuthMode) (hs : List auth.AuthState) (rq : EtcdGrove.apply.IRRModel)
    (log : mvcc.Log) (ar : Loc) (out : EtcdGrove.apply.ApplyOut) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars ⊢
      EtcdGrove.apply.applyResultIs rq true log ar out -∗
      EtcdGrove.apply.adminOut Own γa M hs rq true ar out -∗ EtcdGrove.apply.adminRejErr ar out -∗
      EtcdGrove.apply.applyResultIs rq true log ar out ∗
      EtcdGrove.apply.adminOut Own γa M hs rq true ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) :=
  applyResultIs_notNoSpaceAdmin Own γa M hs rq log ar out

end applyStateOn

end EtcdGrove
end Perennial
#print axioms Perennial.EtcdGrove.server_run
#print axioms Perennial.EtcdGrove.server_start
#print axioms Perennial.EtcdGrove.server_Start
#print axioms Perennial.EtcdGrove.start_gives_views
#print axioms Perennial.EtcdGrove.scheduler_fifo
#print axioms Perennial.EtcdGrove.server_raft_node_start

#print axioms Perennial.EtcdGrove.server_put_on
#print axioms Perennial.EtcdGrove.server_delete_range_on
#print axioms Perennial.EtcdGrove.server_txn_on

#print axioms Perennial.EtcdGrove.apply_kv_entry_pre_on
#print axioms Perennial.EtcdGrove.apply_kv_after_on

#print axioms Perennial.EtcdGrove.server_applied_predeposit_on
#print axioms Perennial.EtcdGrove.server_apply_not_nospace_on
#print axioms Perennial.EtcdGrove.server_uber_kvl
#print axioms Perennial.EtcdGrove.server_uber_kvl_on
