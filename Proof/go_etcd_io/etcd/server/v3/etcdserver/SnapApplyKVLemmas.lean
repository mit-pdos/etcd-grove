/-
**What step 4 of `srvSnapApplied_of_walk` reads off the restored log** (D22 receiver epochs, S8d,
`SnapApplyKV.lean`): the sole writer's log facts (`soleLog`) and the restored state's leases (none)
from `restoreLogOk`, and the KV's resources `apply.kvOwn` at the snapshot's environment.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreChunks

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-- A log of non-empty revisions has at least a change per revision. -/
theorem logCh_ge_length (R : mvcc.Log) (h : ∀ cs ∈ R, cs ≠ []) : R.length ≤ mvcc.logCh R := by
  induction R with
  | nil => simp
  | cons cs R ih =>
    have h1 : cs ≠ [] := h cs (List.mem_cons_self ..)
    have h2 := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have h3 : 0 < cs.length := List.length_pos_iff.2 h1
    unfold mvcc.logCh at h2 ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- **The restored log is a sole writer's** (`soleLog`): `NewStore`'s two revisions, then a
change per revision (`restoreLogOk`'s first conjunct). -/
theorem soleLog_restore (R : mvcc.Log) (h : mvcc.restoreLogOk R) : txn.soleLog ([[], []] ++ R) := by
  have := logCh_ge_length R h.1
  have hc : mvcc.logCh ([[], []] ++ R) = mvcc.logCh R := by
    unfold mvcc.logCh; simp
  unfold txn.soleLog
  rw [hc]; simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The restored log's puts carry no lease (`restoreLogOk`'s third conjunct). -/
theorem logNoLease_restore (R : mvcc.Log) (h : mvcc.restoreLogOk R) :
    mvcc.LogNoLease ([[], []] ++ R) := by
  intro cs hcs c hc k v l hcl
  rcases List.mem_append.1 hcs with hcs | hcs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
    rcases hcs with rfl | rfl <;> simp at hc
  · exact h.2.2 cs hcs c hc k v l hcl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **No lease is needed of the restored state** (`leasesKnown []`). -/
theorem leasesKnown_restore (R : mvcc.Log) (h : mvcc.restoreLogOk R) :
    ⊢ txn.leasesKnown (GF := GF) [] (mvcc.stateAfter ([[], []] ++ R)) := by
  have hz := mvcc.stateAfter_leaseZero _ (logNoLease_restore R h)
  unfold txn.leasesKnown txn.leasesOk
  iintro !> %l %hl
  iunfold txn.leaseOk
  ipureintro
  left
  obtain ⟨kv, hkv, rfl⟩ := List.mem_map.1 hl
  exact hz kv hkv

/-- **The KV's resources at the snapshot's environment** and the restored log: the writer's from
the watchable store's sole writer (`watchWriter`, of the logical names) at the restored physical
names `p'`, the writer's own from the restore's reader token. -/
theorem kvOwn_snap (E : apply.AEnv GF) (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (ci : Loc)
    (p' : mvcc.PhysNames) (g : GoFunc) (γB : backend.BNames) (al ast lp cl : Loc)
    (d' : mvcc.KBReal) (γw : mvcc.WsNames) (ws : Loc) (R : mvcc.Log)
    (hkb' : p'.kb = some d') (hγw : γw.st = E.γ) (hwq : E.γ.watchQ = true)
    (hRok : mvcc.restoreLogOk R) (hrb : receiptBound GF ≤ 2 ^ 48) :
    mvcc.isWatchableStore ws E.s γw ∗ mvcc.storeReader E.s E.γ ∗
      mvcc.writerFrag (γw.st.withPhys p') ∗ mvcc.watchWriter γw ([[], []] ++ R) ∗
      (mvcc.storeRT (γw.st.withPhys p') -∗ mvcc.writerOwn (γw.st.withPhys p')) ∗
      mvcc.bkRTx d'.γB d'.P d'.be ∗
      lease.leaseOwn E.γ.leases [] ∅ ∗ lease.lessorRdOf E.γ.leases ∗ lease.leaseRevokers E.γ.leases [] ∗ E.RD ⊢
    apply.kvOwn (snapE E γ' TM' ci p' g γB al ast lp cl d'.be) ([[], []] ++ R) := by
  iintro ⟨#Hws, Hrd, Hfrag, Hww, Hwo, Hrt, Hlo, Hlr, Hrv, HRD⟩
  iunfold apply.kvOwn
  rw [storeReader_snapE, snapE_γ, snapE_s, snapE_RD]
  rw [← hγw]
  iunfold mvcc.watchWriter at Hww
  icases Hww with ⟨#Hc, Htoks, Hhalf⟩
  ihave Hwo := Hwo $$ [Hrt]
  · unfold mvcc.storeRT
    rw [show (γw.st.withPhys p').kb = some d' from hkb', kbRT_some]
    iexact Hrt
  iframe Hrd HRD Hwo
  isplitl [Htoks Hhalf Hfrag]
  · unfold txn.kvWriter txn.soleWriter
    isplitl [Htoks]
    · rw [mvcc.idxCert_withPhys]
      iframe Hc
      have hb : txn.soleBudget ([[], []] ++ R) = mvcc.wBudget ([[], []] ++ R) := rfl
      rw [hb, show (γw.st.withPhys p').revs = γw.st.revs from rfl]
      isplitl [Htoks]
      · iexact Htoks
      ipureintro; exact ⟨soleLog_restore R hRok, hrb⟩
    isplitr [Hfrag]
    · have hq : (γw.st.withPhys p').watchQ = true := by rw [hγw]; exact hwq
      iapply (txn.wlogOwn_watch E.s (γw.st.withPhys p') _ hq).2
      iexists ws, { γw with st := γw.st.withPhys p' }
      rw [mvcc.isWatchableStore_withPhys, mvcc.idxCert_withPhys]
      iframe Hws Hhalf Hc
      ipureintro; rfl
    · iexact Hfrag
  · unfold apply.leasesLive lease.lessorUser
    iexists []
    ihave #Hlk := leasesKnown_restore (GF := GF) R hRok
    iframe Hlk
    rw [show (γw.st.withPhys p').leases = γw.st.leases from rfl]
    ihave Hlo := lease.leaseOwn_eq (mvcc.leaseItemsOf_zero _
      (mvcc.stateAfter_leaseZero _ (logNoLease_restore R hRok))).symm $$ Hlo
    iframe Hlo Hlr Hrv

end proof

end EtcdGrove
end Perennial
