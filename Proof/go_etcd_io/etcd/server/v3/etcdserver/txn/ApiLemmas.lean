/-
The txn proofs' lemmas over mvcc's API (strict M1, 2026-11-05): a transaction's and a store
handle's dynamic type meets its interface's contracts (from `shapes.law`), keeping the resource.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

/-- A reachable state's log has `NewStore`'s two revisions. -/
theorem txn.reach_len (σ : MvccState) (h : mvcc.api.MvccReachable σ) : 2 ≤ σ.log.length := by
  induction h with
  | start => decide
  | notify σ pend _ _ _ ih => exact ih
  | commit σ _ ih =>
    unfold mvcc.api.MvccState.commitPending mvcc.commitLog
    split
    · exact ih
    · simp only [List.length_append, List.length_singleton]; omega
  | compact σ r _ _ _ _ _ ih => exact ih

/-- A reachable state's compaction revision is in `[-1, rev]`. -/
theorem txn.reach_crev (σ : MvccState) (h : mvcc.api.MvccReachable σ) :
    -1 ≤ σ.crev ∧ σ.crev ≤ (σ.rev : Int) := by
  induction h with
  | start => simp [mvcc.api.mvccStart, mvcc.api.MvccState.rev]
  | notify σ pend _ _ _ ih => exact ih
  | commit σ _ ih =>
    refine ⟨ih.1, ?_⟩
    have : σ.rev ≤ σ.commitPending.rev := by
      unfold mvcc.api.MvccState.commitPending mvcc.api.MvccState.rev mvcc.commitLog
      split <;> simp <;> omega
    have h2 : σ.commitPending.crev = σ.crev := rfl
    rw [h2]; omega
  | compact σ r _ _ h1 h2 h3 ih =>
    exact ⟨by simp [mvcc.api.MvccState.compactTo]; omega, by
      simpa [mvcc.api.MvccState.compactTo, mvcc.api.MvccState.rev] using h3⟩

/-- A prefix of the last revision's changes keeps the log well formed (a copy of mvcc's
`WatchScan.lean` `LogWf'.take_last`, internal, until the API re-exports it). -/
theorem txn.logWf'_take_last {ilog : mvcc.Log} {pend rest : List mvcc.Change}
    (h : mvcc.LogWf' (ilog ++ [pend ++ rest])) : mvcc.LogWf' (ilog ++ [pend]) := by
  refine ⟨fun _ => ?_, fun r cs i k hr hi => ?_⟩
  · have := h.1 (by simp)
    rcases Nat.eq_zero_or_pos ilog.length with h0 | hpos
    · rw [List.length_eq_zero_iff] at h0; subst h0
      simp at this ⊢
      exact this.1
    · rw [List.getElem?_append_left hpos] at this ⊢; exact this
  · by_cases hlt : r < ilog.length
    · rw [List.getElem?_append_left hlt] at hr
      have := h.2 r cs i k (by rw [List.getElem?_append_left hlt]; exact hr) hi
      rw [mvcc.stateAt_append_lt _ _ (by omega)] at this ⊢
      exact this
    · have hr' : r = ilog.length := by
        have := (List.getElem?_eq_some_iff.1 hr).1; simp at this; omega
      subst hr'
      rw [List.getElem?_append_right (Nat.le_refl _)] at hr
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      have hi' : (pend ++ rest)[i]? = some (.del k) := by
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1]; exact hi
      have := h.2 ilog.length (pend ++ rest) i k
        (by rw [List.getElem?_append_right (Nat.le_refl _)]; simp) hi'
      have htake : (pend ++ rest).take i = pend.take i := by
        rw [List.take_append_of_le_length (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hi).1)]
      rw [htake] at this
      rcases Nat.eq_zero_or_pos ilog.length with h0 | hpos
      · -- revision `0` is empty: no delete in it
        rw [List.length_eq_zero_iff] at h0; subst h0
        have h1 := h.1 (by simp)
        simp at h1
        rw [h1.1] at hi; simp at hi
      rw [mvcc.stateAt_append_lt _ _ (by omega)] at this ⊢
      exact this

/-- **A delete's log before it** (gap F's fix: `Txn.DeleteRange`'s post gives the log after the
delete well formed and small): `LogOk` of the log before (`LogWf'.take_last`). -/
theorem txn.logOk_of_del (σ : MvccState) (pend ds : List mvcc.Change) (h : txn.Reach σ)
    (hwf : mvcc.LogWf' (σ.log ++ [pend ++ ds]))
    (hcs : ∀ cs ∈ σ.log ++ [pend ++ ds], cs.length < 2 ^ 63) : txn.LogOk (σ.log ++ [pend]) := by
  have h3 := h.2
  refine txn.LogOk.of_cert ⟨txn.logWf'_take_last hwf, by simp; omega, ?_⟩ (by simp)
  intro cs hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hcs cs (List.mem_append_left _ hc)
  · simp only [List.mem_singleton] at hc; subst hc
    have := hcs (cs ++ ds) (by simp)
    simp only [List.length_append] at this; omega

/-- A transaction's compaction revision is at most the revision it reads at. -/
theorem txn.crev_le_readRev (k : MTxn) (h : txn.Reach k.state) :
    k.state.crev ≤ sint.Z k.readRev := by
  have hc := txn.reach_crev _ h.1
  have h3 := h.2
  cases k with
  | read σ =>
    simp only [mvcc.api.MTxn.state, mvcc.api.MTxn.readRev] at hc h3 ⊢
    have : sint.Z (W64 (σ.rev : Int)) = (σ.rev : Int) := by unfold mvcc.api.MvccState.rev; word
    omega
  | write σ pend =>
    simp only [mvcc.api.MTxn.state, mvcc.api.MTxn.readRev] at hc h3 ⊢
    have h4 : σ.rev ≤ mvcc.writeRev σ.log pend := by
      unfold mvcc.writeRev mvcc.api.MvccState.rev; split <;> omega
    have : sint.Z (W64 ((mvcc.writeRev σ.log pend : Nat) : Int)) = (mvcc.writeRev σ.log pend : Int) := by
      have : mvcc.writeRev σ.log pend ≤ σ.log.length := by unfold mvcc.writeRev; split <;> omega
      word
    omega

/-- A read transaction reads the state after its log. -/
theorem txn.kindState_read (σ : MvccState) (h : txn.Reach σ) :
    txn.kindState (.read σ) = mvcc.stateAfter σ.log := by
  have h2 := txn.reach_len _ h.1
  have h3 := h.2
  have hne : σ.log ≠ [] := by intro h0; rw [h0] at h2; simp at h2
  unfold txn.kindState
  simp only [mvcc.api.MTxn.readLog, mvcc.api.MTxn.readRev]
  have : ((σ.rev : Nat) : Int) = (σ.log.length : Int) - 1 := by
    unfold mvcc.api.MvccState.rev; omega
  rw [this]
  exact txn.stateAt_lastRev σ.log hne (by omega)

/-- A transaction's read revision is not negative. -/
theorem txn.readRev_nonneg (k : MTxn) (h : txn.Reach k.state) : 0 ≤ sint.Z k.readRev := by
  have h3 := h.2
  cases k with
  | read σ =>
    simp only [mvcc.api.MTxn.state, mvcc.api.MTxn.readRev] at h3 ⊢
    unfold mvcc.api.MvccState.rev; word
  | write σ pend =>
    simp only [mvcc.api.MTxn.state, mvcc.api.MTxn.readRev] at h3 ⊢
    have : mvcc.writeRev σ.log pend ≤ σ.log.length := by unfold mvcc.writeRev; split <;> omega
    word

/-- No change appended: the same transaction. -/
theorem txn.MTxn.append_nil (k : MTxn) : txn.MTxn.append k [] = k := by
  cases k <;> simp [txn.MTxn.append]

/-- A read transaction's changes leave it as it is. -/
theorem txn.MTxn.append_read (k : MTxn) (X : List mvcc.Change) (h : txn.MTxn.isRead k = true) :
    txn.MTxn.append k X = k := by
  cases k <;> simp_all [txn.MTxn.append, txn.MTxn.isRead]

/-- A write transaction's state after more changes. -/
theorem txn.mstate_append (k : MTxn) (X : List mvcc.Change) (h : txn.MTxn.isRead k = false) :
    txn.mstate (txn.MTxn.append k X) =
      mvcc.applyChanges (W64 (k.state.log.length : Int)) (txn.mstate k) X := by
  cases k with
  | read σ => simp [txn.MTxn.isRead] at h
  | write σ pend =>
    simp only [txn.MTxn.append, txn.mstate, mvcc.api.MTxn.state]
    exact txn.pendState_append σ.log pend X

/-- The state a transaction reads after changes (none for a read transaction). -/
theorem txn.kindState_append (k : MTxn) (X : List mvcc.Change) (h : txn.Reach k.state)
    (hX : txn.MTxn.isRead k = true → X = []) :
    txn.kindState (txn.MTxn.append k X) =
      mvcc.applyChanges (W64 (k.state.log.length : Int)) (txn.mstate k) X := by
  have h2 := txn.reach_len _ h.1
  have h3 := h.2
  cases k with
  | read σ =>
    rw [hX rfl]
    simp only [txn.MTxn.append, txn.mstate, mvcc.api.MTxn.state] at *
    exact txn.kindState_read σ h
  | write σ pend =>
    simp only [txn.MTxn.append, txn.mstate, mvcc.api.MTxn.state] at *
    have hne : σ.log ≠ [] := by intro h0; rw [h0] at h2; simp at h2
    rw [txn.kindState_write σ (pend ++ X) hne (by omega)]
    exact txn.pendState_append σ.log pend X

/-- A transaction's begin state after changes. -/
theorem txn.MTxn.append_state (k : MTxn) (chs : List mvcc.Change) :
    (txn.MTxn.append k chs).state = k.state := by cases k <;> rfl

/-! ### The lessor window of a run (auth-lease S4 item 7b) -/

namespace txn
section win
variable [GooseExts]

theorem winOps_append (w : Option lease.LWin) (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (a b : List TxnOp),
      WinOps w s0 r s (a ++ b) ↔
        WinOps w s0 r s a ∧ WinOps w s0 r (mvcc.applyChanges r s (srvOps s0 r s a).1) b
  | s, [], b => by simp [WinOps, srvOps_nil, applyChanges_nil']
  | s, x :: a, b => by
    rw [List.cons_append]
    simp only [WinOps]
    rw [winOps_append w s0 r _ a b, srvOps_cons]
    simp only [applyChanges_append]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- The window premises of the operations from the `i`-th on, at the state the first `i` left. -/
theorem winOps_drop' (w : Option lease.LWin) (s0 : List EtcdKv) (r : w64) (s : List EtcdKv)
    (ops : List TxnOp) (i : Nat) (h : WinOps w s0 r s ops) :
    WinOps w s0 r (mvcc.applyChanges r s (srvOps s0 r s (ops.take i)).1) (ops.drop i) := by
  rw [← List.take_append_drop i ops, winOps_append] at h
  exact h.2

theorem winOps_drop (w : Option lease.LWin) (s0 : List EtcdKv) (r : w64) (s : List EtcdKv)
    (ops : List TxnOp) (i : Nat) (op : TxnOp) (h : ops[i]? = some op) :
    WinOps w s0 r s (ops.drop i) ↔
      WinOp w s0 r s op ∧ WinOps w s0 r (mvcc.applyChanges r s (srvOp s0 r s op).1) (ops.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 h).1, (List.getElem?_eq_some_iff.1 h).2]
  simp [WinOps]

/-- A nested transaction's window premise: its chosen branch's. -/
theorem winOp_txn (w : Option lease.LWin) (s0 : List EtcdKv) (r : w64) (s : List EtcdKv)
    (cs : List CmpModel) (ts es : List TxnOp) (h : WinOp w s0 r s (.txn cs ts es)) :
    WinOps w s0 r s (if cs.all (cmpHolds s0) then ts else es) := by
  simp only [WinOp] at h
  cases hb : cs.all (cmpHolds s0) <;> rw [hb] at h <;> simpa using h

/-- Gets only: within any window. -/
theorem winOps_gets (w : Option lease.LWin) (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), (∀ op ∈ ops, opIsGet op = true) → WinOps w s0 r s ops
  | _, [], _ => trivial
  | s, op :: ops, h => by
    refine ⟨?_, winOps_gets w s0 r _ ops (fun o ho => h o (List.mem_cons_of_mem _ ho))⟩
    have := h op List.mem_cons_self
    cases op <;> simp_all [opIsGet, WinOp]

/-- A put's window premise (any of the three kinds): its change moves the items toward the target. -/
theorem winOp_put_et (w : Option lease.LWin) (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (o : OpFull)
    (h : WinOp w s0 r s (putTxnOp o)) :
    lease.winMove w (mvcc.leaseItemsOf s)
      (mvcc.leaseItemsOf (mvcc.applyChanges r s [putChangeOf o (mvcc.findKey o.key s)])) := by
  have h2 : WinOp w s0 r s (putTxnOp o) = lease.winMove w (mvcc.leaseItemsOf s)
      (mvcc.leaseItemsOf (mvcc.applyChanges r s (srvOp s0 r s (putTxnOp o)).1)) := by
    unfold putTxnOp; split <;> (try split) <;> simp only [WinOp]
  rw [h2, srvOp_putTxnOp] at h; exact h

/-- **The pending item map is the committed one's after the commit** (item 7b F2: the owner's items at `End` are the
items of the log it commits). -/
theorem pendItems_commitLog (ilog : mvcc.Log) (pend : List mvcc.Change) :
    mvcc.pendItems ilog pend = mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog ilog pend)) := by
  unfold mvcc.commitLog
  split
  · subst_vars; rfl
  · rw [mvcc.stateAfter_append]

/-- **A put request's item map**: the pending one after its change, from the begin state's. -/
theorem pendItems_putChangeOf (ilog : mvcc.Log) (o : OpFull) :
    mvcc.pendItems ilog [putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))] =
      putItemsOf (mvcc.pendItems ilog []) o := by
  have h := mvcc.pendItems_put ilog [] o.key (putValOf o (mvcc.findKey o.key (mvcc.stateAfter ilog)))
    (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))) (putItemsOf (mvcc.pendItems ilog []) o)
  rw [List.nil_append] at h
  apply h
  · intro it hk
    have hne : go_etcd_io.etcd.server.v3.lease.LeaseItem.mk o.key ≠ it := by
      intro he; subst he; exact hk rfl
    unfold putItemsOf
    split
    · rfl
    · split
      · simp [GMap.lookup_delete_iff, hne]
      · simp [GMap.lookup_insert_eq_iff, hne]
  · unfold putItemsOf putLeaseOf
    cases hil : o.ignoreLease
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · simp
      · simp
    · simp only [↓reduceIte]
      show (mvcc.leaseItemsOf (mvcc.stateAfter ilog)).lookup _ = _
      rw [mvcc.leaseItemsOf_lookup]
      cases hf : mvcc.findKey o.key (mvcc.stateAfter ilog) with
      | none => simp
      | some kv => simp [mvcc.kvLease]

end win
end txn

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **A transaction's read log and revision** (gap A's fix, `Txn.Range`'s post: the read log well
formed, its revisions small): `KindOk`, what relates mvcc's index answers to the state read. -/
theorem txn.kindOk_of (k : MTxn) (h : txn.Reach k.state) (hwf : mvcc.LogWf' k.readLog)
    (hcs : ∀ cs ∈ k.readLog, cs.length < 2 ^ 63) : txn.KindOk k := by
  have h2 := txn.reach_len _ h.1
  have h3 := h.2
  cases k with
  | read σ =>
    simp only [mvcc.api.MTxn.state] at h2 h3
    have hne : σ.log ≠ [] := by intro h0; rw [h0] at h2; simp at h2
    have hl : (mvcc.api.MTxn.read σ).readLog.length < 2 ^ 63 := by
      simp only [mvcc.api.MTxn.readLog]; omega
    refine ⟨txn.LogOk.of_cert ⟨hwf, hl, hcs⟩
      (by simpa [mvcc.api.MTxn.readLog] using hne), ?_, ?_⟩ <;>
    · simp only [mvcc.api.MTxn.readRev, mvcc.api.MTxn.readLog, mvcc.api.MvccState.rev]; word
  | write σ pend =>
    simp only [mvcc.api.MTxn.state] at h2 h3
    have hl : (mvcc.api.MTxn.write σ pend).readLog.length < 2 ^ 63 := by
      simp only [mvcc.api.MTxn.readLog, List.length_append, List.length_singleton]; omega
    refine ⟨txn.LogOk.of_cert ⟨hwf, hl, hcs⟩ (by simp [mvcc.api.MTxn.readLog]), ?_, ?_⟩ <;>
    · simp only [mvcc.api.MTxn.readRev, mvcc.api.MTxn.readLog, mvcc.writeRev, List.length_append,
        List.length_singleton]
      split <;> word

/-- **A transaction is an interface value whose type meets `TxnWrite`'s contracts**
(`shapes.law`), the transaction kept. -/
theorem txn.mvccTxn_shape (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) :
    mvcc.api.mvccTxn (GF := GF) t γ trace k ⊢
      ⌜∃ ty v, t = interface.mkOk ty v ∧ mvcc.api.isTxn (GF := GF) ty v⌝ ∗
        mvcc.api.mvccTxn t γ trace k :=
  persistent_entails_right (hsh.2.2.1 t γ trace k)

/-- **A store handle is an interface value whose type meets `KV`'s contracts** (`shapes.law`),
the handle kept. -/
theorem txn.isMvcc_shape (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (kv : GoInterface) (γ : MvccName) :
    mvcc.api.isMvcc (GF := GF) kv γ ⊢
      ⌜∃ ty v, kv = interface.mkOk ty v ∧ mvcc.api.isKV (GF := GF) ty v⌝ ∗ mvcc.api.isMvcc kv γ :=
  persistent_entails_right (hsh.1 kv γ)

/-- **The caller's read update, with what txn records of its state** (`clients-txn.md` §3, the
wrapper): given the store's handle, the caller's update at a read becomes one whose commit also
gives `Reach σ` (`mvccState_reachable.law` at the state in hand). -/
theorem txn.readAU_reach (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (kv : GoInterface) (γ : MvccName) (Q : MvccState → IProp GF) :
    mvcc.api.isMvcc kv γ ⊢
      txn.readAU γ Q -∗ txn.readAU γ (fun σ => iprop(Q σ ∗ ⌜txn.Reach σ⌝)) := by
  haveI := hpers.1 kv γ
  iintro #Hkv Hau
  unfold txn.readAU
  iauintro
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%x, Hx, Hcl⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists x
  iframe Hx
  isplit
  · iintro Hx
    icases Hcl with ⟨Hab, -⟩
    iapply Hab $$ Hx
  · iintro Hx
    icases (persistent_entails_right (hreach kv γ x)) $$ [$Hkv $Hx] with ⟨%Hr, -, Hx⟩
    icases Hcl with ⟨-, Hco⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
    imod Hco $$ Hx with HQ
    imodintro
    iframe HQ
    ipureintro; exact Hr

/-- **The caller's begin update, with what txn records of its state**: the commit also gives
`Reach σ` and the promised `σ.pending = none`. -/
theorem txn.beginAU_reach (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (kv : GoInterface) (γ : MvccName) (R : MvccState → IProp GF) :
    mvcc.api.isMvcc kv γ ⊢
      txn.beginAU γ R -∗
        txn.beginAU γ (fun σ => iprop(⌜txn.Reach σ ∧ σ.pending = none⌝ ∗ R σ)) := by
  haveI := hpers.1 kv γ
  iintro #Hkv Hau
  unfold txn.beginAU
  iauintro
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%x, Hx, Hcl⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists x
  iframe Hx
  isplit
  · iintro Hx
    icases Hcl with ⟨Hab, -⟩
    iapply Hab $$ Hx
  · iintro ⟨%Hpn, Hx⟩
    icases (persistent_entails_right (hreach kv γ x)) $$ [$Hkv $Hx] with ⟨%Hr, -, Hx⟩
    icases Hcl with ⟨-, Hco⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
    imod Hco $$ [Hx] with HR
    · iframe Hx; ipureintro; exact Hpn
    imodintro
    iframe HR
    ipureintro; exact ⟨Hr, Hpn⟩

/-- **A read transaction's `End`**: the reader token back (`Txn.End.contract` at a read
transaction, whose backend arguments do not matter). -/
theorem txn.end_read {ty : go.GoType} {v : val}
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (γ : MvccName) (trace : Loc) (σ : MvccState) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.api.mvccTxn (interface.mkOk ty v) γ trace (.read σ) }}
      (App (Val #(methods ty go!"End" v)) (Val #()))
    {{ RET #(); mvcc.api.mvccReaders γ 1 }} := by
  have hB : Nonempty mvcc.api.MvccStorage := by
    refine ⟨mvcc.api.etcdStorage ⟨?_, ∅, 0, 0, null, ?_, false⟩⟩
    · constructor <;> first | exact default | (constructor <;> exact default)
    · exact default
  obtain ⟨B⟩ := hB
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iapply (hEnd γ trace (.read σ) 1 B iprop(True) iprop(True)) $$ [Htx]
  · iframe Hpkg Htx
  inext
  iintro ⟨Hrd, -⟩
  iapply HΦ
  iframe Hrd

/-- **A write transaction's `End`**: the caller's two commit updates (`commitAU`, `Txn.End`'s
shape), the batch lock's invariant `P` given, the backend share and the reader
token back. -/
theorem txn.end_write {ty : go.GoType} {v : val}
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (γ : MvccName) (trace : Loc) (σ₀ : MvccState) (pend : List mvcc.Change) (q : Qp)
    (B : mvcc.api.MvccStorage) (P Q : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.api.mvccTxn (interface.mkOk ty v) γ trace (.write σ₀ pend) ∗
        mvcc.api.mvccBackend γ q B P ∗ P ∗ txn.commitAU γ σ₀ pend Q }}
      (App (Val #(methods ty go!"End" v)) (Val #()))
    {{ RET #(); mvcc.api.mvccReaders γ 1 ∗ mvcc.api.mvccBackend γ q B P ∗ Q }} := by
  have h := hEnd γ trace (.write σ₀ pend) q B P Q
  dsimp only at h
  iintro %Φ ⟨#Hpkg, Htx, Hbk, HP, Hau⟩ HΦ
  iapply h $$ [Htx Hbk HP Hau]
  · iframe Hpkg Htx Hbk HP
    iexact Hau
  inext
  iintro ⟨Hrd, Hbk, HQ⟩
  iapply HΦ
  iframe Hrd Hbk HQ

/-- A read transaction after changes is the read transaction. -/
theorem txn.mvccTxn_append_read (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn)
    (X : List mvcc.Change) (h : txn.MTxn.isRead k = true) :
    mvcc.api.mvccTxn (GF := GF) t γ trace (txn.MTxn.append k X) ⊢ mvcc.api.mvccTxn t γ trace k := by
  rw [txn.MTxn.append_read k X h]

end lemmas

end EtcdGrove
end Perennial
