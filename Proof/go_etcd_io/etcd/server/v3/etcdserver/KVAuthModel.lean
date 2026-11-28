/-
**The KV invariant in the auth mode `on`** (the auth plan's E2q, 2026-10-26; `notes/decisions.md`,
"E2p of the auth plan" and "E2q of the auth plan"). The KV invariant `kvInv` keeps the start chain
with the auth layer off (`KVChainOff.lean`), and its model `kvModel` folds `kvEntry` at that one
chain, where the auth layer lets every request through. With auth on, a committed entry's effect
depends on the auth store's state when the entry is applied, so the mode `on` has a model of its
own that folds the auth state with the KV log:

- **An admitted admin entry** (`apply.adminKindOk`: `SetUp`'s five kinds) changes the auth state
  only: by the admin step of its kind (`auth/Steps.lean`) if its principal is admin-permitted at
  that state (`auth.adminOk`, `authApplierV3.Apply`'s `IsAdminPermitted`), else not at all
  (`adminStateR`, `adminNext`). It leaves the KV log alone (`kvEntryOn_admin`).
- **A KV entry** (a put, a delete, a range, a transaction) writes iff the auth state at that point
  grants its principal every permission the request needs (`kvGranted`: for each of `reqPerms`,
  auth disabled, or a revision that is not `0` and not below the store's -- `ErrAuthOldRevision`
  -- and a user with the root role or on whose permissions Go's verdict, `auth.coversX`, passes; a
  request needing none is let through); otherwise it is refused and leaves the log alone.
- Every other entry is today's (`kvEntry`).

**Why a function of the committed log, and why determinacy is a premise of the log.** The KV
invariant ties the KV state (`etcdKV`'s ghost variable) to the model of raft's *committed* log
(`srvRLog`), and a client's update fires when its entry commits (`kvAu`), before any member applies
it. So the model must be a function of the committed log; recording the auth state per entry in
ghost state (E2p's other option) would make the committer, raft's commit, choose an outcome the
apply thread must later reproduce, which only works if the outcome is a function of the prefix. In
Go it is (every member applies the same prefix), but two of the model's admin steps are relations
(`userGrantRoleR`: the user's roles after `sort.Strings`; `UserAdd`'s `ErrNoPasswordUser`, a refusal
decided by the request's password choice, which the request model keeps since E2t:
`UserAddModel.pwSure` rules it out; `roleGrantPermissionR` was a third until E3z, when the fork's
fix made it a function), so the model's step is the *unique* successor where there is one (`adminNext`), and the
mode-`on` log premise (`detLogOn`) asks every committed admin entry to have a unique successor at
the state it is applied at (the workload's to establish, as `plainLog` is today). A KV entry's check
needs nothing of the log: Go's verdict (`auth.coversX`, the permission cache's interval trees
modelled exactly) is a function of the auth state for every request (N1b-1; until then the log had
to keep every check of the shape `auth.reqShape`, `kvDet`, outside of which the verdict was not
stated). The apply thread's actual outcome is then
the model's (`adminNext_of_det`, `kvEntryOn_of_granted`, `kvEntryOn_of_refused`).

**The range end.** `reqPerms` takes a request's range end as the model has it (`OpFull`'s
`base.rangeEnd`); the checks see the request's bytes, which differ from the model's only for a
non-`nil` empty `RangeEnd`, which no wire request has (`apply.authEndOf`, A1).

**Additive.** Nothing here changes `kvInv`, `kvModel`, `plainLog` or `kvWork`: the mode `on` has its
own (`kvInvOn`, `kvModelOn`, `plainLogOn`, `kvWorkOn`), and `kvInvM on` is `kvInv` at `on = false`
by definition (`kvInvM_false`), so every mode-`off` statement keeps its text.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVChainOff
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchKVL
public import Proof.go_etcd_io.etcd.server.v3.auth.Steps
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **The auth history along the requested log `L`** (the auth-mode merge's 5b): the start's
state `st₀`, then the state after each recorded admin entry (`admEntry`). Its last state is the
auth state after `L` (`admStates_last`). -/
noncomputable def admStates (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) :
    List auth.AuthState :=
  admStatesR γk.c0 γk.ch0 (st₀, γk.log0, []) L

/-- A log of no normal entries (the bootstrap log's configuration changes) has the start's
history. -/
theorem admStates_conf (γk : KVNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (h : ∀ m ∈ A, m.typ ≠ W32 0) : admStates γk st₀ A = [st₀] := by
  have key : ∀ (B : List EntryModel) (acc : OnState × List auth.AuthState),
      (∀ m ∈ B, m.typ ≠ W32 0) → (B.foldl (admStep γk.c0 γk.ch0) acc).2 = acc.2 := by
    intro B
    induction B with
    | nil => intro acc _; rfl
    | cons m B ih =>
      intro acc hB
      rw [List.foldl_cons, ih _ (fun x hx => hB x (List.mem_cons_of_mem _ hx))]
      unfold admStep
      rw [if_neg (fun ⟨ht, _⟩ => hB m List.mem_cons_self ht)]
  unfold admStates admStatesR
  exact key A _ h

/-- An entry of a request needing no admin permission leaves the history as it is. -/
theorem admStates_snoc_noadmin (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode e.data = some rq)
    (hna : apply.needAdminPermission rq = false) :
    admStates γk st₀ (L ++ [e]) = admStates γk st₀ L := by
  unfold admStates
  apply admStatesR_snoc_other
  rintro ⟨-, -, rq', hdec', -, ha, -⟩
  rw [hdec] at hdec'; cases hdec'
  rw [adminDispatchKind_of_needAdmin_false rq hna] at ha; cases ha

end pure

/-! ## The mode-`on` log premises -/

section pure2
variable [GooseExts]

/-- **A leased transaction in the auth-on log** (auth-lease S3a): plain but for its puts' leases (its gets
at revision `0`, no `IgnoreLease`, `IgnoreValue` as a plain one's, a put's lease free): `txn.txnLeased`. -/
def txnPlainL (t : TxnModel) : Prop := txn.txnLeased t

theorem txnPlainL_of_plain (t : TxnModel) (h : txn.txnPlain t) : txnPlainL t :=
  txn.txnLeased_of_plain t h

/-- A leased transaction of the auth-on log is one of the txn specs' (`txn.txnLeased`). -/
theorem txnLeased_of_txnPlainL (t : TxnModel) (h : txnPlainL t) : txn.txnLeased t := h

/-- **A request of the auth-on log at the lease mode `lm`** (auth-lease S3a): a plain request
(`plainReq`), or, at the revocable mode, a put with any lease or a transaction plain but for its puts'
leases (`txnPlainL`), as `plainCover` otherwise (no side-effect-free field, no admin field). -/
def plainReqL (lm : lease.Mode) (rq : apply.IRRModel) : Prop :=
  plainReq rq ∨ (lm = .revocable ∧ apply.noSideEffect rq = false ∧
    apply.needAdminPermission rq = false ∧
    (apply.dispatchKind rq = .put ∨
      (apply.dispatchKind rq = .txn ∧ ∀ t, rq.txn = some t → txnPlainL t)))

/-- At the lease mode `none` a request of the auth-on log is a plain one. -/
theorem plainReqL_none (rq : apply.IRRModel) : plainReqL .none rq ↔ plainReq rq := by
  unfold plainReqL
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · cases h
  · exact Or.inl

theorem plainReqL_of_plainReq (lm : lease.Mode) (rq : apply.IRRModel) (h : plainReq rq) :
    plainReqL lm rq := Or.inl h

/-- (auth-lease S3a2 §4) **What the apply arms read of a request of the auth-on log**: no side-effect-free
field, no admin field, a kind the proposers send (`putgetKind`); a plain request's or a leased one's. -/
theorem plainReqL_facts (lm : lease.Mode) (rq : apply.IRRModel) (h : plainReqL lm rq) :
    apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false ∧
      putgetKind (apply.dispatchKind rq) := by
  rcases h with ⟨hc, hk⟩ | ⟨-, hns, hna, hk | ⟨hk, -⟩⟩
  · refine ⟨?_, ?_, hk⟩ <;> unfold plainCover at hc <;>
      rcases hk with hk | hk | hk | hk | hk <;> rw [hk] at hc <;> simp only at hc <;>
      first | exact hc.1 | exact hc.2.1 | exact hc.2
  · exact ⟨hns, hna, Or.inl hk⟩
  · exact ⟨hns, hna, Or.inr (Or.inr (Or.inl hk))⟩

/-- A request of the auth-on log is covered (`kvCover`). -/
theorem kvCover_of_plainReqL (lm : lease.Mode) (rq : apply.IRRModel) (h : plainReqL lm rq) : kvCover rq := by
  rcases h with ⟨hc, -⟩ | ⟨-, hns, hna, hk | ⟨hk, -⟩⟩
  · exact kvCover_of_plainCover rq hc
  · unfold kvCover; rw [hk]; exact ⟨hns, hna⟩
  · unfold kvCover; rw [hk]; exact ⟨hns, hna⟩

/-- A request of the auth-on log is no compaction. -/
theorem plainReqL_nonCmp (lm : lease.Mode) (rq : apply.IRRModel) (h : plainReqL lm rq) :
    apply.dispatchKind rq ≠ .compaction := by
  have hk := (plainReqL_facts lm rq h).2.2
  unfold putgetKind at hk
  rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;> decide

/-- A request of the auth-on log is plain, or a put or a transaction (a KV kind). -/
theorem plainReqL_cases (lm : lease.Mode) (rq : apply.IRRModel) (h : plainReqL lm rq) :
    plainReq rq ∨ (apply.dispatchKind rq = .put ∨ apply.dispatchKind rq = .txn) := by
  rcases h with h | ⟨-, -, -, hk | ⟨hk, -⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr hk)

/-- The widest lease mode admits every request of the auth-on log. -/
theorem plainReqL_revocable (lm : lease.Mode) (rq : apply.IRRModel) (h : plainReqL lm rq) :
    plainReqL .revocable rq := by
  rcases h with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨rfl, h⟩

/-- **An entry of the mode-`on` log at the lease mode `lm`** (auth-lease S3a): a normal entry with data
decodes to a request of the auth-on log (`plainReqL lm`), with (E3o) no range end `"\x00"`
(`noZeroEnds`; N1b-1: no shape of its checks, Go's verdict being exact for every request), or to a grant
or a revocation the mode admits
(`grantPropOk`, `revokePropOk`), or to an admitted admin request (`apply.adminKindOk`) without a read
field (`noSideEffect` false, E3o). -/
def plainEntryOn (lm : lease.Mode) (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    ((plainReqL lm rq ∧ noZeroEnds rq) ∨ grantPropOk lm rq ∨ revokePropOk lm rq) ∨
      (apply.adminKindOk rq ∧ apply.noSideEffect rq = false)

/-- Every entry of the mode-`on` log at the lease mode `lm`. -/
def plainLogOn (lm : lease.Mode) (A : List EntryModel) : Prop := ∀ m ∈ A, plainEntryOn lm m

/-- **The keys' leases are live** (auth-lease S3a; derived from the log): every key the log's state
attaches to a lease `id` has `id` in the table's ids. -/
def keysLeasesLive (s : OnState) : Prop :=
  ∀ (k : GoString) (id : w64), mvcc.leaseItemsOf (mvcc.stateAfter s.2.1) !! ⟨k⟩ = some id →
    id ∈ s.2.2.ids

/-- Every key-value of the state `s` has lease `0` or one of `ids`. -/
def liveSt (ids : List w64) (s : List EtcdKv) : Prop :=
  ∀ kv ∈ s, kv.lease = W64 0 ∨ kv.lease ∈ ids

theorem liveSt_mono {ids ids' : List w64} (h : ∀ i ∈ ids, i ∈ ids') {s : List EtcdKv}
    (hs : liveSt ids s) : liveSt ids' s :=
  fun kv hk => (hs kv hk).imp_right (h _)

theorem liveSt_applyChange {ids : List w64} {s : List EtcdKv} (hs : liveSt ids s) (r : w64)
    (c : mvcc.Change) (hc : ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0 ∨ l ∈ ids) :
    liveSt ids (mvcc.applyChange r s c) := by
  cases c with
  | put k v l =>
    intro kv hkv
    simp only [mvcc.applyChange, putKv] at hkv
    rcases btInsert_mem hkv with rfl | h
    · split <;> exact hc k v l rfl
    · exact hs kv h
  | del k =>
    intro kv hkv
    exact hs kv (List.mem_filter.1 hkv).1

theorem liveSt_applyChanges {ids : List w64} (r : w64) :
    ∀ (cs : List mvcc.Change) {s : List EtcdKv}, liveSt ids s →
      (∀ c ∈ cs, ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0 ∨ l ∈ ids) →
      liveSt ids (mvcc.applyChanges r s cs)
  | [], _, hs, _ => hs
  | c :: cs, s, hs, hc => by
    unfold mvcc.applyChanges
    rw [List.foldl_cons]
    exact liveSt_applyChanges r cs (liveSt_applyChange hs r c (hc c (by simp)))
      (fun c' h => hc c' (by simp [h]))

theorem liveSt_findKey {ids : List w64} {s : List EtcdKv} (hs : liveSt ids s) (k : GoString) :
    ((mvcc.findKey k s).map EtcdKv.lease).getD (W64 0) = W64 0 ∨
      ((mvcc.findKey k s).map EtcdKv.lease).getD (W64 0) ∈ ids := by
  cases hf : mvcc.findKey k s with
  | none => left; rfl
  | some kv => exact hs kv (List.mem_of_find?_eq_some hf)

/-- Deletions alone keep it. -/
theorem liveSt_dels {ids : List w64} {s : List EtcdKv} (hs : liveSt ids s) (r : w64)
    (cs : List mvcc.Change) (hd : ∀ c ∈ cs, ∃ k, c = .del k) : liveSt ids (mvcc.applyChanges r s cs) :=
  liveSt_applyChanges r cs hs (fun c hc k v l he => by
    obtain ⟨k', rfl⟩ := hd c hc; cases he)

mutual
theorem liveSt_srvOp (s0 : List EtcdKv) (ids : List w64) (r : w64) :
    ∀ (s : List EtcdKv) (op : TxnOp), liveSt ids s → txn.PathLeaseOk s0 ids op →
      liveSt ids (mvcc.applyChanges r s (txn.srvOp s0 r s op).1)
  | s, .get o, hs, _ => by simpa [txn.srvOp, mvcc.applyChanges] using hs
  | s, .put k v l, hs, hp => by
    simp only [txn.srvOp]
    exact liveSt_applyChanges r _ hs (fun c hc k' v' l' he => by
      simp only [List.mem_singleton] at hc; subst hc; cases he; exact hp)
  | s, .putKeep k v, hs, _ => by
    simp only [txn.srvOp]
    exact liveSt_applyChanges r _ hs (fun c hc k' v' l' he => by
      simp only [List.mem_singleton] at hc; subst hc; cases he; exact liveSt_findKey hs k)
  | s, .putIgnVal k lo, hs, hp => by
    simp only [txn.srvOp]
    refine liveSt_applyChanges r _ hs (fun c hc k' v' l' he => ?_)
    simp only [List.mem_singleton] at hc; subst hc; cases he
    cases lo with
    | none => exact liveSt_findKey hs k
    | some l => exact hp
  | s, .delete o, hs, _ => by
    simp only [txn.srvOp]
    exact liveSt_dels hs r _ (fun c hc => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hc; exact ⟨_, rfl⟩)
  | s, .txn cs ts es, hs, hp => by
    rw [txn.srvOp_txn]
    simp only [txn.PathLeaseOk] at hp
    cases hc : cs.all (cmpHolds s0)
    · rw [hc] at hp; simp only [Bool.false_eq_true, ↓reduceIte]
      exact liveSt_srvOps s0 ids r s es hs hp
    · rw [hc] at hp; simp only [↓reduceIte]
      exact liveSt_srvOps s0 ids r s ts hs hp

theorem liveSt_srvOps (s0 : List EtcdKv) (ids : List w64) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), liveSt ids s → txn.PathsLeaseOk s0 ids ops →
      liveSt ids (mvcc.applyChanges r s (txn.srvOps s0 r s ops).1)
  | s, [], hs, _ => by simpa [txn.srvOps, mvcc.applyChanges] using hs
  | s, op :: ops, hs, hp => by
    rw [txn.srvOps_cons]
    simp only [txn.PathsLeaseOk] at hp
    rw [txn.applyChanges_append]
    exact liveSt_srvOps s0 ids r _ ops (liveSt_srvOp s0 ids r s op hs hp.1) hp.2
end

theorem liveSt_commitLog {ids : List w64} {log : mvcc.Log} (hs : liveSt ids (mvcc.stateAfter log))
    (cs : List mvcc.Change) (h : liveSt ids (mvcc.applyChanges (W64 log.length) (mvcc.stateAfter log) cs)) :
    liveSt ids (mvcc.stateAfter (mvcc.commitLog log cs)) := by
  unfold mvcc.commitLog
  split
  · exact hs
  · rw [txn.stateAfter_snoc]; exact h

/-- A revocation's deletions leave only key-values of the state with another lease. -/
theorem revoke_mem (r : w64) (s : List EtcdKv) (id : w64) :
    ∀ kv ∈ mvcc.applyChanges r s (revokeChanges s id), kv ∈ s ∧ kv.lease ≠ id := by
  intro kv hkv
  have hm : revokeChanges s id = ((s.filter (fun v => v.lease = id)).map EtcdKv.key).map mvcc.Change.del := by
    unfold revokeChanges; rw [List.map_map]; rfl
  rw [hm, txn.applyChanges_dels] at hkv
  obtain ⟨hin, hk⟩ := List.mem_filter.1 hkv
  refine ⟨hin, fun he => ?_⟩
  have : kv.key ∈ (s.filter (fun v => v.lease = id)).map EtcdKv.key :=
    List.mem_map.2 ⟨kv, List.mem_filter.2 ⟨hin, by simp [he]⟩, rfl⟩
  simp [this] at hk

/-- The table without `id` keeps the leases of a state whose key-values avoid `id`. -/
theorem liveSt_revoke (lt : LeaseTable) (id : w64) (s : List EtcdKv) (hs : liveSt lt.ids s)
    (s' : List EtcdKv) (h : ∀ kv ∈ s', kv ∈ s ∧ kv.lease ≠ id) :
    liveSt (LeaseTable.ids (lt.filter (fun p => decide (p.fst ≠ id)))) s' := by
  intro kv hkv
  obtain ⟨hin, hne⟩ := h kv hkv
  rcases hs kv hin with h0 | hl
  · exact Or.inl h0
  · right
    unfold LeaseTable.ids at hl ⊢
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hl
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simp [hpe, hne]⟩, hpe⟩

open Classical in
/-- **The backend keeps the keys' leases live** (`backendLog`/`backendTable`). -/
theorem liveSt_backend (lt : LeaseTable) (rq : apply.IRRModel) (log : mvcc.Log)
    (hs : liveSt lt.ids (mvcc.stateAfter log)) :
    liveSt (backendTable rq lt).ids (mvcc.stateAfter (backendLog lt rq log)) := by
  unfold backendLog backendTable
  cases hk : apply.dispatchKind rq <;> simp only [] <;> try exact hs
  case put =>
    cases hop : rq.put with
    | none => exact hs
    | some op =>
      simp only []
      split
      · exact hs
      · rename_i hm
        split
        · exact hs
        · rw [txn.stateAfter_snoc]
          refine liveSt_applyChanges _ _ hs (fun c hc k v l he => ?_)
          simp only [List.mem_singleton] at hc; subst hc
          unfold txn.putChangeOf at he; cases he
          unfold txn.putLeaseOf
          split
          · exact liveSt_findKey hs op.key
          · unfold leaseMissingIn at hm
            by_cases h0 : op.leaseID = W64 0
            · left; exact h0
            · right; exact Classical.byContradiction (fun hn => hm ⟨h0, hn⟩)
  case deleteRange =>
    cases hop : rq.deleteRange with
    | none => exact hs
    | some op =>
      exact liveSt_commitLog hs _ (liveSt_dels hs _ _ (fun c hc => by
        unfold txn.delChanges at hc; obtain ⟨v, -, rfl⟩ := List.mem_map.1 hc; exact ⟨_, rfl⟩))
  case txn =>
    cases hop : rq.txn with
    | none => exact hs
    | some t =>
      simp only []
      split
      · rename_i hok
        exact liveSt_commitLog hs _ (liveSt_srvOps _ _ _ _ _ hs hok.2)
      · exact hs
  case leaseGrant =>
    cases hop : rq.leaseGrant with
    | none => exact hs
    | some g =>
      simp only []
      split
      · exact liveSt_mono (fun i hi => by
          unfold LeaseTable.ids at hi ⊢; rw [List.map_append, List.mem_append]; exact Or.inl hi) hs
      · exact hs
  case leaseRevoke =>
    cases hop : rq.leaseRevoke with
    | none => exact hs
    | some id =>
      simp only []
      split
      · rename_i hin
        refine liveSt_revoke lt id (mvcc.stateAfter log) hs _ ?_
        unfold mvcc.commitLog
        split
        · rename_i h0
          intro kv hkv
          refine ⟨hkv, fun he => ?_⟩
          have : mvcc.Change.del kv.key ∈ revokeChanges (mvcc.stateAfter log) id :=
            List.mem_map.2 ⟨kv, List.mem_filter.2 ⟨hkv, by simp [he]⟩, rfl⟩
          rw [h0] at this; cases this
        · rw [txn.stateAfter_snoc]
          exact revoke_mem _ _ _
      · exact hs

/-- A request other than a revocation only grows the chain's table. -/
theorem chainTable_sup (rq : apply.IRRModel) (hk : apply.dispatchKind rq ≠ .leaseRevoke) :
    ∀ (c : apply.Chain) (lt : LeaseTable), ∀ i ∈ lt.ids, i ∈ (chainTable c rq lt).ids
  | .backend, lt, i, hi => by
    simp only [chainTable]
    unfold backendTable
    cases hk' : apply.dispatchKind rq <;> simp only [] <;> try exact hi
    case leaseGrant =>
      cases rq.leaseGrant with
      | none => exact hi
      | some g =>
        simp only []
        split
        · unfold LeaseTable.ids at hi ⊢; rw [List.map_append, List.mem_append]; exact Or.inl hi
        · exact hi
    case leaseRevoke => exact absurd hk' hk
  | .auth _ c, lt, i, hi => by simp only [chainTable]; exact chainTable_sup rq hk c lt i hi
  | .quota c, lt, i, hi => by simp only [chainTable]; exact chainTable_sup rq hk c lt i hi
  | .capped c, lt, i, hi => by
    simp only [chainTable]; split
    · exact hi
    · exact chainTable_sup rq hk c lt i hi
  | .corrupt c, lt, i, hi => by
    simp only [chainTable]; split
    · exact hi
    · exact chainTable_sup rq hk c lt i hi

theorem liveSt_chain (rq : apply.IRRModel) :
    ∀ (c : apply.Chain) (lt : LeaseTable) (log : mvcc.Log), liveSt lt.ids (mvcc.stateAfter log) →
      liveSt (chainTable c rq lt).ids (mvcc.stateAfter (chainLog c rq lt log))
  | .backend, lt, log, hs => liveSt_backend lt rq log hs
  | .auth _ c, lt, log, hs => by simp only [chainTable, chainLog]; exact liveSt_chain rq c lt log hs
  | .quota c, lt, log, hs => by simp only [chainTable, chainLog]; exact liveSt_chain rq c lt log hs
  | .capped c, lt, log, hs => by
    simp only [chainTable, chainLog]; split
    · exact hs
    · exact liveSt_chain rq c lt log hs
  | .corrupt c, lt, log, hs => by
    simp only [chainTable, chainLog]; split
    · exact hs
    · exact liveSt_chain rq c lt log hs

theorem liveSt_dispatch (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (lt : LeaseTable)
    (log : mvcc.Log) (hs : liveSt lt.ids (mvcc.stateAfter log)) :
    liveSt (dispatchTable c rq v3 lt).ids (mvcc.stateAfter (dispatchLog c rq v3 lt log)) := by
  unfold dispatchLog dispatchTable
  split
  · exact hs
  · split
    · exact liveSt_chain rq c lt log hs
    · rename_i hst
      refine liveSt_mono (chainTable_sup rq (fun h => hst (by rw [h]; rfl)) c lt) hs

theorem liveSt_kvEntry (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log) (m : EntryModel)
    (hs : liveSt lt.ids (mvcc.stateAfter log)) :
    liveSt (kvTable c₀ ch lt m).ids (mvcc.stateAfter (kvEntry c₀ ch lt log m)) := by
  unfold kvEntry kvTable
  by_cases ht : m.typ = W32 0
  · simp only [ht, ↓reduceIte]
    by_cases hd : m.data = []
    · simp only [hd, ↓reduceIte]; exact hs
    · simp only [hd, ↓reduceIte]
      cases apply.irrDecode m.data with
      | none => exact hs
      | some rq => exact liveSt_dispatch ch rq _ lt log hs
  · simp only [ht, ↓reduceIte]; exact hs

/-- **The mode-`on` step keeps the keys' leases live.** -/
theorem liveSt_kvEntryOn (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel)
    (hs : liveSt s.2.2.ids (mvcc.stateAfter s.2.1)) :
    liveSt (kvEntryOn c₀ ch s m).2.2.ids (mvcc.stateAfter (kvEntryOn c₀ ch s m).2.1) := by
  unfold kvEntryOn
  split
  · split
    · split
      · exact hs
      · split
        · exact hs
        · split
          · exact hs
          · exact liveSt_kvEntry c₀ ch s.2.2 s.2.1 m hs
    · exact hs
  · exact liveSt_kvEntry c₀ ch s.2.2 s.2.1 m hs

theorem liveSt_kvRaftOfOn (c₀ : w64) (ch : apply.Chain) :
    ∀ (A : List EntryModel) (s : OnState), liveSt s.2.2.ids (mvcc.stateAfter s.2.1) →
      liveSt (kvRaftOfOn c₀ ch s A).2.2.ids (mvcc.stateAfter (kvRaftOfOn c₀ ch s A).2.1)
  | [], s, hs => hs
  | m :: A, s, hs => liveSt_kvRaftOfOn c₀ ch A (kvEntryOn c₀ ch s m) (liveSt_kvEntryOn c₀ ch s m hs)

theorem keysLeasesLive_of_liveSt (s : OnState) (h : liveSt s.2.2.ids (mvcc.stateAfter s.2.1)) :
    keysLeasesLive s := by
  intro k id hk
  have hk' : ((mvcc.findKey k (mvcc.stateAfter s.2.1)).bind mvcc.kvLease) = some id := hk
  cases hf : mvcc.findKey k (mvcc.stateAfter s.2.1) with
  | none => rw [hf] at hk'; cases hk'
  | some kv =>
    rw [hf] at hk'
    simp only [Option.bind_some, mvcc.kvLease] at hk'
    split at hk'
    · cases hk'
    · rename_i h0
      cases hk'
      rcases h kv (List.mem_of_find?_eq_some hf) with hz | hin
      · exact absurd hz h0
      · exact hin

/-- **The keys' leases are live in the mode-`on` model of any log** from a start whose log attaches
no key to a lease (auth-lease S3a, Draft rev 5 §1/§5): a leased put applies only at a live lease, a
revocation deletes its keys with its id, a refused request changes neither. -/
theorem keysLeasesLive_kvRaftOfOn (c₀ : w64) (ch : apply.Chain) (st₀ : auth.AuthState) (log₀ : mvcc.Log)
    (A : List EntryModel) (h : mvcc.LogNoLease log₀) :
    keysLeasesLive (kvRaftOfOn c₀ ch (st₀, log₀, []) A) :=
  keysLeasesLive_of_liveSt _ (liveSt_kvRaftOfOn c₀ ch A _
    (fun kv hkv => Or.inl (mvcc.stateAfter_leaseZero log₀ h kv hkv)))

/-- At the lease mode `none`, an entry of the mode-`on` log is what it was (no lease request). -/
theorem plainEntryOn_none (m : EntryModel) (h : plainEntryOn .none m) :
    m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
      (plainReq rq ∧ noZeroEnds rq) ∨
        (apply.adminKindOk rq ∧ apply.noSideEffect rq = false) := by
  intro ht hd rq hrq
  rcases h ht hd rq hrq with ((⟨h1, h2⟩ | h | h) | h)
  · exact Or.inl ⟨(plainReqL_none rq).1 h1, h2⟩
  · exact absurd h (grantPropOk_false rq)
  · exact absurd h (revokePropOk_none rq)
  · exact Or.inr h

/-- An admitted admin request is not of a kind the auth layer's KV checks see (`authKVKind`). -/
theorem adminKindOk_nonAuthKV (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    apply.authKVKind (apply.dispatchKind rq) = false := by
  unfold apply.adminKindOk at h
  unfold apply.authKVKind
  split at h <;> simp_all [apply.isKVKind]

/-- An admitted admin request is no grant. -/
theorem adminKindOk_nonGrant (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    apply.dispatchKind rq ≠ .leaseGrant := by
  intro hk
  unfold apply.adminKindOk at h
  rw [hk] at h
  exact h

/-- A plain request is of a KV kind. -/
theorem plainReq_authKV (rq : apply.IRRModel) (h : plainReq rq) :
    apply.authKVKind (apply.dispatchKind rq) = apply.isKVKind (apply.dispatchKind rq) := by
  obtain ⟨-, hk⟩ := h
  unfold apply.authKVKind
  rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;> rfl

/-- A request of the auth-on log is no grant. -/
theorem plainReqL_nonGrant (lm : lease.Mode) (rq : apply.IRRModel) (h : plainReqL lm rq) :
    apply.dispatchKind rq ≠ .leaseGrant := by
  rcases h with ⟨-, hk⟩ | ⟨-, -, -, hk | ⟨hk, -⟩⟩
  · rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;> decide
  · rw [hk]; decide
  · rw [hk]; decide

/-- **At the lease mode `none`, an entry of the mode-`on` log changes no table** (a plain request, or an
admin one, which is no write). -/
theorem kvTable_plainOn_none (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (m : EntryModel)
    (hp : plainEntryOn .none m) : kvTable c₀ ch lt m = lt := by
  unfold kvTable
  split
  · rename_i ht
    split
    · rfl
    · rename_i hd
      split
      · rename_i rq hdec
        unfold dispatchTable
        split
        · rfl
        · rcases plainEntryOn_none m hp ht hd rq hdec with h | h
          · exact chainTable_plain rq lt h.1.1 ch
          · have hw : ¬ writeKind (apply.dispatchKind rq) := by
              have hk := h.1
              unfold apply.adminKindOk at hk
              split at hk <;> simp_all [writeKind]
            exact chainTable_nonwrite rq lt hw ch
      · rfl
  · rfl

/-- At the lease mode `none`, every entry of the mode-`on` log keeps the table. -/
theorem kvRaftOfOn_table_none (c₀ : w64) (ch : apply.Chain) :
    ∀ (s : OnState) (A : List EntryModel), plainLogOn .none A → (kvRaftOfOn c₀ ch s A).2.2 = s.2.2
  | _, [], _ => rfl
  | s, m :: A, h => by
    have hm := h m (List.mem_cons_self ..)
    have hstep : (kvEntryOn c₀ ch s m).2.2 = s.2.2 := by
      unfold kvEntryOn
      split
      · split
        · split
          · rfl
          · split
            · rfl
            · split
              · rfl
              · exact kvTable_plainOn_none c₀ ch _ m hm
        · rfl
      · exact kvTable_plainOn_none c₀ ch _ m hm
    show (kvRaftOfOn c₀ ch (kvEntryOn c₀ ch s m) A).2.2 = s.2.2
    rw [kvRaftOfOn_table_none c₀ ch _ A (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')), hstep]

/-- **The entry is determinate at the state `s` it is applied at** (see the header): an admin entry
above `c₀` has one successor (`authDet`). (Until N1b-1 a KV entry's or a revocation's check had to be
decided too, `kvDet`: Go's verdict `auth.coversX` is now a function of the state for every request.) -/
def entryDetOn (c₀ : w64) (s : OnState) (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    uint.Z c₀ < uint.Z m.index → apply.needAdminPermission rq = true → authDet rq s.1

/-- **Every entry of `A` is determinate at the state the model reaches before it.** -/
def detLogOn (c₀ : w64) (ch : apply.Chain) (s₀ : OnState) (A : List EntryModel) :
    Prop :=
  ∀ (i : Nat) (m : EntryModel), A[i]? = some m → entryDetOn c₀ (kvRaftOfOn c₀ ch s₀ (A.take i)) m

theorem detLogOn_nil (c₀ : w64) (ch : apply.Chain) (s₀ : OnState) :
    detLogOn c₀ ch s₀ [] := by
  intro i m h; simp at h

/-- `detLogOn` of a snoc: the prefix's, and the new entry's at the prefix's model. -/
theorem detLogOn_snoc (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) (m : EntryModel) (hA : detLogOn c₀ ch s₀ A)
    (hm : entryDetOn c₀ (kvRaftOfOn c₀ ch s₀ A) m) : detLogOn c₀ ch s₀ (A ++ [m]) := by
  intro i m' h
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rw [List.getElem?_append_left hi] at h
    rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
    exact hA i m' h
  · rw [List.getElem?_append_right hi] at h
    have hi' : i = A.length := by
      have := (List.getElem?_eq_some_iff.mp h).1
      simp only [List.length_singleton] at this
      omega
    subst hi'
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.take_left' rfl]
    exact hm

/-- `detLogOn` of a prefix. -/
theorem detLogOn_prefix (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (B L : List EntryModel) (hp : B <+: L) (h : detLogOn c₀ ch s₀ L) : detLogOn c₀ ch s₀ B := by
  obtain ⟨C, rfl⟩ := hp
  intro i m hm
  have hi : i < B.length := (List.getElem?_eq_some_iff.mp hm).1
  have h' := h i m (by rw [List.getElem?_append_left hi]; exact hm)
  rwa [List.take_append_of_le_length (Nat.le_of_lt hi)] at h'

/-- **The last entry of a determinate log is determinate at the state before it** (what the apply
thread needs of the entry it applies). -/
theorem detLogOn_last (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) (m : EntryModel) (h : detLogOn c₀ ch s₀ (A ++ [m])) :
    entryDetOn c₀ (kvRaftOfOn c₀ ch s₀ A) m := by
  have h' := h A.length m (by simp)
  rwa [List.take_left' rfl] at h'

/-- **An entry of a good shape in the mode `on`** at the lease mode `lm` (`entryShape lm`, whose request
clause `rqShape lm` excludes every admin kind, or an admitted admin request with an id). -/
def entryShapeOn (lm : lease.Mode) (m : EntryModel) : Prop :=
  (m.typ = W32 0 → m.data = [] ∨ ∃ rq, apply.irrDecode m.data = some rq ∧
      (∃ id, apply.irrId rq = some id) ∧ (rqShape lm rq ∨ apply.adminKindOk rq)) ∧
    (m.typ ≠ W32 0 → ccIdOf m.data = W64 0)

/-- Every entry of a log has a good shape in the mode `on`. -/
def logShapeOn (lm : lease.Mode) (L : List EntryModel) : Prop := ∀ m ∈ L, entryShapeOn lm m

theorem entryShapeOn_of_entryShape (lm : lease.Mode) (m : EntryModel) (h : entryShape lm m) :
    entryShapeOn lm m := by
  refine ⟨fun ht => ?_, h.2⟩
  rcases h.1 ht with h | ⟨rq, hd, hid, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨rq, hd, hid, Or.inl hs⟩

end pure2

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The KV model of the committed log `L` in the mode `on`**, from the start's auth state `st₀`
(the store's state at the server's start) and the start's log. -/
def kvModelOn (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) : mvcc.Log :=
  (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).2.1

theorem kvModelOn_nil (γk : KVNames) (st₀ : auth.AuthState) : kvModelOn γk st₀ [] = γk.log0 := rfl

/-- **The lease table of the committed log `L` in the mode `on`** (auth-lease S3a), from the empty table. -/
def kvLeasesOn (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) : LeaseTable :=
  (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).2.2

theorem kvLeasesOn_nil (γk : KVNames) (st₀ : auth.AuthState) : kvLeasesOn γk st₀ [] = [] := rfl

/-- **At the lease mode `none` the table is empty** (Draft rev 4 §4, r4's named lemma): a log of the mode-`on`
log at `none` grants no lease. -/
theorem kvLeasesOn_none (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (h : plainLogOn .none L) : kvLeasesOn γk st₀ L = [] := by
  unfold kvLeasesOn; rw [kvRaftOfOn_table_none _ _ _ L h]

/-- A log of no normal entries (the bootstrap log's configuration changes) has the empty table. -/
theorem kvLeasesOn_conf (γk : KVNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (h : ∀ m ∈ A, m.typ ≠ W32 0) : kvLeasesOn γk st₀ A = [] := by
  unfold kvLeasesOn; rw [kvRaftOfOn_conf _ _ _ A h]

/-- **The KV state of the committed log `L` in the auth mode `on`**: the mode-`on` model's log and
lease table, from the start's auth state `st₀` (`kvInvOn`'s ghost state). (Auth-lease S3a: moved here
from `ReadOn`, with the table.) -/
@[reducible] def kvStOn (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) : KVState :=
  kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)

/-- **The mode-`on` model at the server's start is the KV model** (N1b-2: `kvModel` is the fold
from `srvAuthSt0`; the twins merge in N2). -/
theorem kvModelOn_srv (γk : KVNames) (L : List EntryModel) : kvModelOn γk srvAuthSt0 L = kvModel γk L :=
  rfl

theorem kvLeasesOn_srv (γk : KVNames) (L : List EntryModel) :
    kvLeasesOn γk srvAuthSt0 L = kvLeases γk L := rfl

theorem kvStOn_srv (γk : KVNames) (L : List EntryModel) : kvStOn γk srvAuthSt0 L = kvModelSt γk L :=
  rfl

/-- **The workload facts of the committed log in the mode `on`** (`kvWork` with `logShapeOn`). -/
def kvWorkOn (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) : IProp GF :=
  iprop(⌜logShapeOn γk.lm L ∧ ccLogOk cfg L ∧ logPutsOk L ∧ mvcc.LogPutsLe etcdKeyMax γk.log0 ∧
      attrLogOk cfg.cfg L⌝ ∗
    [∗list] m ∈ L, entryClaim γk.ids m)

instance kvWorkOn_persistent (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) :
    Persistent (kvWorkOn (GF := GF) cfg γk L) := by
  unfold kvWorkOn; infer_instance

instance kvWorkOn_timeless (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) :
    Timeless (kvWorkOn (GF := GF) cfg γk L) := by
  unfold kvWorkOn; infer_instance

/-- `kvWork` gives `kvWorkOn`. -/
theorem kvWorkOn_of_kvWork (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel)
    (hlg : γk.lg = false) :
    kvWork (GF := GF) cfg γk L ⊢ kvWorkOn cfg γk L := by
  unfold kvWork kvWorkOn
  iintro ⟨%h, #H⟩
  iframe H
  ipureintro
  exact ⟨fun m hm => entryShapeOn_of_entryShape γk.lm m (h.1 m hm), h.2⟩

/-! ### A client's view of the auth history (the auth-mode merge's 5b, 2026-10-29) -/

end defsHF

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A client's view of the auth history** (the auth-mode merge's 5b): half of the mono-list
authority of the history along the requested log (`admStates`; `kvInvOn` holds the other half).
Its holder is the only one who can give the update an admin request recorded in the history needs
(`histAu`), so no such request commits without it. -/
def authHistView (γk : KVNames) (hs : List auth.AuthState) : IProp GF :=
  monoListAuthOwn γk.hist (1 : Qp).half hs

/-- **A lower bound of the auth history** (persistent). -/
def authHistLb (γk : KVNames) (hs : List auth.AuthState) : IProp GF :=
  monoListLbOwn γk.hist hs

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- The namespace of a client's freezable view (`authHistCell`). -/
def authHistN : Namespace := nroot .@ "auth_hist"

/-- **A freezable view's cell, open at `hs`**: its holder's half of the cell's mark, the cell's
history `hs`, not frozen. -/
def authHistOpen (γz : GName) (hs : List auth.AuthState) : IProp GF :=
  dghostVar γz (.own (1 : Qp).half) (false, hs)

/-- **A freezable view's cell, frozen at `hs`** (persistent): the history no longer grows past
`hs` (`authHistFrozen_prefix`). -/
def authHistMark (γz : GName) (hs : List auth.AuthState) : IProp GF :=
  dghostVar γz .discard (true, hs)

/-- **A client's freezable view** (persistent; the auth-mode merge's 5b): an invariant holding the
view at some `hs` and the cell's other half, open (`authHistOpen`'s holder updates it), or frozen
at `hs` (`authHistMark`). Its contents are timeless, so an atomic update's precondition can open
it. -/
def authHistCell (γk : KVNames) (γz : GName) : IProp GF :=
  inv authHistN iprop(∃ hs : List auth.AuthState, authHistView γk hs ∗
    (dghostVar γz (.own (1 : Qp).half) (false, hs) ∨ authHistMark γz hs))

/-- **The auth history frozen at `hs`** (persistent): a client's cell frozen there. -/
def authHistFrozen (γk : KVNames) (γz : GName) (hs : List auth.AuthState) : IProp GF :=
  iprop(authHistCell γk γz ∗ authHistMark γz hs)

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

instance authHistView_timeless (γk : KVNames) (hs : List auth.AuthState) :
    Timeless (authHistView (GF := GF) γk hs) := by
  unfold authHistView; infer_instance

instance authHistLb_persistent (γk : KVNames) (hs : List auth.AuthState) :
    Persistent (authHistLb (GF := GF) γk hs) := by
  unfold authHistLb; infer_instance

instance authHistLb_timeless (γk : KVNames) (hs : List auth.AuthState) :
    Timeless (authHistLb (GF := GF) γk hs) := by
  unfold authHistLb; infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


instance authHistMark_persistent (γz : GName) (hs : List auth.AuthState) :
    Persistent (authHistMark (GF := GF) γz hs) := by
  unfold authHistMark; infer_instance

instance authHistMark_timeless (γz : GName) (hs : List auth.AuthState) :
    Timeless (authHistMark (GF := GF) γz hs) := by
  unfold authHistMark; infer_instance

instance authHistCell_persistent (γk : KVNames) (γz : GName) :
    Persistent (authHistCell (GF := GF) γk γz) := by
  unfold authHistCell; infer_instance

instance authHistFrozen_persistent (γk : KVNames) (γz : GName) (hs : List auth.AuthState) :
    Persistent (authHistFrozen (GF := GF) γk γz hs) := by
  unfold authHistFrozen; infer_instance

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The KV invariant in the mode `on`** (`kvInv`'s, with the mode-`on` model, see the header):
the server's half of the committed log `L` (after `ai0`, consecutive, every entry of the mode-`on`
log and determinate at the state it is applied at, every entry above the start's consistent index)
and the other half of the state's ghost variable at the state of `L`'s mode-`on` model; the start's
chain the base chain with auth **enabled** and no alarm, the start log not empty; the workload
facts (`kvWorkOn`); (5b) the other half of the auth history along `L` (`authHistView`); (the
auth-on pair's F8) the cluster's auth mode on (`SrvRaft.authOn`, `kvInvOn_authOn`); (2026-11-05,
H-rr1) the start and requested logs' size facts (`kvLogSmall`, as `kvInv`'s). (Auth-lease S3a,
2026-11-15) The model on the triple state with its lease table (the state's half at the model's log and
table, `kvLeasesOn`), the log at the cluster's lease mode (`plainLogOn γk.lm`), the start log attaching
no key to a lease (`mvcc.LogNoLease`), and the claim rights of the log's revocable-mode grant ids
(`kvGrantIds`, as `kvInv`'s). The clients' half is kept whatever the mode, unlike `kvInv`'s `kvStQ`. -/
def kvInvOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) : IProp GF :=
  inv kvN iprop(∃ L : List EntryModel,
    srvRLog γ L ∗
    ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)) ∗
    monoListAuthOwn γk.hist (1 : Qp).half (admStates γk st₀ L) ∗
    ⌜plainLogOn γk.lm L ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0, []) L ∧ srvIdxOkW γ.ai0 L ∧
      uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧ γk.ch0 = apply.alarmChain true false false ∧
      (γk.log0 ≠ [] ∧ mvcc.LogNoLease γk.log0) ∧ γ.raft.authOn = true ∧ kvLogSmall γk L⌝ ∗
    kvWorkOn γ.raft γk L ∗ kvGrantIds γk L)

instance kvInvOn_persistent (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    Persistent (kvInvOn (GF := GF) γ γk st₀) := by
  unfold kvInvOn; infer_instance

/-- **The KV invariant in the auth mode `on`**: `kvInv` at `on = false` (by definition:
`kvInvM_false`), `kvInvOn` at `on = true`. -/
def kvInvM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) : IProp GF :=
  match on with
  | false => kvInv γ γk
  | true => kvInvOn γ γk st₀

theorem kvInvM_false (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    kvInvM (GF := GF) false γ γk st₀ = kvInv γ γk := rfl

theorem kvInvM_true (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    kvInvM (GF := GF) true γ γk st₀ = kvInvOn γ γk st₀ := rfl

instance kvInvM_persistent (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (st₀ : auth.AuthState) : Persistent (kvInvM (GF := GF) on γ γk st₀) := by
  cases on <;> unfold kvInvM <;> infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **An admin entry's result tied to its step** (the auth plan's E3x, persistent): for an
admin request, a refused outcome (`authApplierV3.Apply`'s `needAdminPermission` check) names why,
the request's principal not admitted at `st` (`auth.adminOk`; auth-mediation M4, 2026-11-21); a
dispatched one has its result `ar` read-only, whose error `nil` says the step from `st` to `st'`
succeeded (`adminStepOk`); nothing for another request or a skipped entry. What the apply thread
hands the waiter (`resultIsWOn`), at the model's step. -/
def adminTieAr (ar : Loc) (rq : apply.IRRModel) (st st' : auth.AuthState) (out : apply.ApplyOut) :
    IProp GF :=
  iprop(⌜apply.needAdminPermission rq = false ∨ out = .skipped⌝ ∨
    ⌜out = .rejected ∧ ¬ auth.adminOk st (some (auth.authInfoM (apply.principalOf rq)))⌝ ∨
    (⌜∃ o b, out = .dispatched o b⌝ ∗
      ∃ v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result, ar ↦□ v ∗
        ⌜v.Err' = GoInterface.nil → adminStepOk rq st st'⌝))

instance adminTieAr_persistent (ar : Loc) (rq : apply.IRRModel) (st st' : auth.AuthState)
    (out : apply.ApplyOut) : Persistent (adminTieAr (GF := GF) ar rq st st' out) := by
  unfold adminTieAr; infer_instance

/-- Of a request needing no admin permission, the tie is free. -/
theorem adminTieAr_nonAdmin (ar : Loc) (rq : apply.IRRModel) (st st' : auth.AuthState)
    (out : apply.ApplyOut) (h : apply.needAdminPermission rq = false) :
    ⊢ adminTieAr (GF := GF) ar rq st st' out := by
  iunfold adminTieAr
  ileft
  ipureintro
  exact Or.inl h

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The mode-`on` KV invariant's start chain has the auth layer on** (`kvInv_ch0_off`'s
counterpart): unlike `kvInv`, it agrees with `NewServer.specM true`'s premise on the start chain. -/
theorem kvInvOn_ch0 (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ ={⊤}=∗ ⌜γk.ch0 = apply.alarmChain true false false⌝ := by
  iintro #Hinv
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw, HG⟩
  imod Hclose $$ [HL Hσ Hh HG] with -
  · inext; iexists L; iframe HL Hσ Hh Hw HG; ipureintro; exact Hok
  imodintro
  ipureintro
  exact Hok.2.2.2.2.1

/-- **The mode-`on` KV invariant's cluster runs auth on** (the auth-on pair's F8): the member's mode
the cluster's (`SrvRaft.authOn`, the image certificate the network carries). -/
theorem kvInvOn_authOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ ={⊤}=∗ ⌜γ.raft.authOn = true⌝ := by
  iintro #Hinv
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw, HG⟩
  imod Hclose $$ [HL Hσ Hh HG] with -
  · inext; iexists L; iframe HL Hσ Hh Hw HG; ipureintro; exact Hok
  imodintro
  ipureintro
  exact Hok.2.2.2.2.2.2.1

/-- **The KV invariant's cluster runs auth off** (the auth-on pair's F8; `kvInvOn_authOn`'s). -/
theorem kvInv_authOn (γ : ServerRaftNames) (γk : KVNames) :
    ⊢ kvInv (GF := GF) γ γk ={⊤}=∗ ⌜γ.raft.authOn = false⌝ := by
  iintro #Hinv
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw, HG⟩
  imod Hclose $$ [HL Hσ HG] with -
  · inext; iexists L; iframe HL Hσ Hw HG; ipureintro; exact Hok
  imodintro
  ipureintro
  exact Hok.2.2.2.2.2.2.2.1

/-- **The member's KV invariant in the mode `on` ties the cluster's mode to it**. -/
theorem kvInvM_authOn (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    ⊢ kvInvM (GF := GF) on γ γk st₀ ={⊤}=∗ ⌜γ.raft.authOn = on⌝ := by
  cases on
  · exact kvInv_authOn γ γk
  · exact kvInvOn_authOn γ γk st₀

/-- **The mode-`on` KV invariant can be allocated** at the empty committed log (as `kvInv`'s, at
the server's start): the server's half of the empty log, the state's half at the start log, the
start chain with auth on, the start log not empty and the consistent index within the start's; (5b)
the history's half at the start's state. So
`kvInvOn` is satisfiable, unlike `kvInv` at a mode-`on` chain (`kvInv_ch0_on_false`). -/
theorem kvInvOn_alloc (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (E : CoPset)
    (hch : γk.ch0 = apply.alarmChain true false false) (hlog : γk.log0 ≠ [])
    (hln : mvcc.LogNoLease γk.log0)
    (hlk : mvcc.LogPutsLe etcdKeyMax γk.log0)
    (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0) (hao : γ.raft.authOn = true)
    (hl0 : γk.log0.length ≤ 2 ^ 61) (hpo : kvPfxOk γk) :
    ⊢ srvRLog (GF := GF) γ [] -∗ ghostVar γk.st (1 : Qp).half (kvStateOf γk.log0 []) -∗
      monoListAuthOwn γk.hist (1 : Qp).half [st₀] ={E}=∗ kvInvOn γ γk st₀ := by
  iintro HL Hσ Hh
  iunfold kvInvOn
  iapply inv_alloc
  inext
  iexists []
  rw [kvModelOn_nil, kvLeasesOn_nil]
  isplitl [HL]
  · iexact HL
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hh]
  · rw [show admStates γk st₀ [] = [st₀] from rfl]; iexact Hh
  isplitr
  · ipureintro
    refine ⟨fun m hm => by simp at hm, detLogOn_nil _ _ _, ?_, hc, hch, ⟨hlog, hln⟩, hao, hl0,
      by simp⟩
    intro n m hm; simp at hm
  isplitr
  · iunfold kvWorkOn
    isplitr
    · ipureintro
      exact ⟨fun m hm => by simp at hm, fun m hm => by simp at hm, fun m hm => by simp at hm, hlk,
        fun m hm => by simp at hm⟩
    · iapply BigSepL.bigSepL_nil.2
      iempintro
  · iapply kvGrantIds_nil γk [] (logRevGrantIds_none _ _ (fun m hm => by simp at hm)) hpo

/-- **One entry on that is no revocable-mode grant** (`kvGrantIds_snoc` without a grant id). -/
theorem kvGrantIds_snoc_keep (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (h : entryRevGrantId γk.lm e = none) :
    kvGrantIds (GF := GF) γk L ⊢ kvGrantIds γk (L ++ [e]) := by
  iintro HG
  iunfold kvGrantIds at HG
  icases HG with ⟨%U, %HU, HUs⟩
  iunfold kvGrantIds
  iexists U
  iframe HUs
  ipureintro
  rw [logRevGrantIds_snoc, h]
  simpa using HU

/-- An entry whose request is no grant has no revocable-mode grant id. -/
theorem entryRevGrantId_nonGrant (lm : lease.Mode) (e : EntryModel)
    (h : e.typ = W32 0 → ∀ rq, apply.irrDecode e.data = some rq →
      apply.dispatchKind rq ≠ .leaseGrant) :
    entryRevGrantId lm e = none := by
  unfold entryRevGrantId
  split
  · rename_i ht
    cases hd : apply.irrDecode e.data with
    | none => rfl
    | some rq =>
      simp only [Option.bind_some]
      unfold rqRevGrantId
      rw [if_neg (fun hc => h ht rq hd hc.2)]
  · rfl

/-! ### The auth history's laws (the auth-mode merge's 5b) -/

end lemmas

section lemmasHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The whole auth history is the view and the invariant's half. -/
theorem authHist_split (γk : KVNames) (l : List auth.AuthState) :
    monoListAuthOwn (GF := GF) γk.hist 1 l ⊢
      authHistView γk l ∗ monoListAuthOwn γk.hist (1 : Qp).half l := by
  have h := (monoListAuthOwn_fractional (GF := GF) γk.hist l).fractional (1 : Qp).half
    (1 : Qp).half
  rw [Qp.half_add_half] at h
  unfold authHistView
  exact h.1

end lemmasHF

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The history's two halves agree, and update together by an append. -/
theorem authHist_halves_update (γk : KVNames) (l l' x : List auth.AuthState) :
    ⊢ monoListAuthOwn (GF := GF) γk.hist (1 : Qp).half l -∗
      monoListAuthOwn γk.hist (1 : Qp).half l' ==∗
      ⌜l = l'⌝ ∗ monoListAuthOwn γk.hist (1 : Qp).half (l ++ x) ∗
        monoListAuthOwn γk.hist (1 : Qp).half (l ++ x) := by
  have hsplit : ∀ l₀ : List auth.AuthState, monoListAuthOwn (GF := GF) γk.hist 1 l₀ ⊣⊢
      monoListAuthOwn γk.hist (1 : Qp).half l₀ ∗ monoListAuthOwn γk.hist (1 : Qp).half l₀ := by
    intro l₀
    have h := (monoListAuthOwn_fractional (GF := GF) γk.hist l₀).fractional (1 : Qp).half
      (1 : Qp).half
    rw [Qp.half_add_half] at h
    exact h
  iintro H1 H2
  ihave %Hag := monoListAuthOwn_agree γk.hist _ _ l l' $$ H1 H2
  obtain ⟨-, rfl⟩ := Hag
  ihave H := (hsplit l).2 $$ [H1 H2]
  · iframe H1 H2
  imod (monoListAuthOwn_update_app (γ := γk.hist) (l := l) x) $$ H with ⟨H, -⟩
  icases (hsplit (l ++ x)).1 $$ H with ⟨H1, H2⟩
  imodintro
  iframe H1 H2
  ipureintro; rfl

theorem authHistView_lb (γk : KVNames) (hs : List auth.AuthState) :
    authHistView (GF := GF) γk hs ⊢ authHistLb γk hs := by
  unfold authHistView authHistLb
  exact monoListLbOwn_get γk.hist _ hs

theorem authHistView_prefix (γk : KVNames) (hs hs' : List auth.AuthState) :
    authHistView (GF := GF) γk hs ∗ authHistLb γk hs' ⊢ ⌜hs' <+: hs⌝ := by
  unfold authHistView authHistLb
  iintro ⟨H1, H2⟩
  ihave %H := mono_list_auth_lb_valid γk.hist _ hs hs' $$ H1 H2
  ipureintro; exact H.2

/-- **A view becomes a freezable cell**, open at its history (`authHistOpen`). -/
theorem authHistCell_alloc (γk : KVNames) (hs : List auth.AuthState) (E : CoPset) :
    ⊢ authHistView (GF := GF) γk hs ={E}=∗ ∃ γz, authHistCell γk γz ∗ authHistOpen γz hs := by
  iintro Hv
  imod (dghostVar_alloc (GF := GF) (false, hs)) with ⟨%γz, Hz⟩
  have h := (dghostVar_fractional (GF := GF) γz (false, hs)).fractional (1 : Qp).half
    (1 : Qp).half
  rw [Qp.half_add_half] at h
  icases h.1 $$ Hz with ⟨Hz1, Hz2⟩
  imod (inv_alloc authHistN E iprop(∃ hs' : List auth.AuthState, authHistView γk hs' ∗
    (dghostVar γz (.own (1 : Qp).half) (false, hs') ∨ authHistMark γz hs'))) $$ [Hv Hz1]
    with #Hc
  · inext; iexists hs; iframe Hv; ileft; iexact Hz1
  imodintro
  iexists γz
  unfold authHistCell authHistOpen
  iframe Hc Hz2

/-- The cell's two open halves agree, and move together to a new history. -/
theorem authHistOpen_update (γz : GName) (hs hs' new : List auth.AuthState) :
    ⊢ authHistOpen (GF := GF) γz hs -∗ dghostVar γz (.own (1 : Qp).half) (false, hs') ==∗
      ⌜hs = hs'⌝ ∗ authHistOpen γz new ∗ dghostVar γz (.own (1 : Qp).half) (false, new) := by
  unfold authHistOpen
  iintro H1 H2
  ihave %Hag := dghostVar_agree γz _ _ _ _ $$ H1 H2
  imod (dghostVar_update_halves (false, new) γz _ _) $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iframe H1 H2
  ipureintro; exact (Prod.mk.inj Hag).2

/-- **Freezing**: the cell's two open halves become the mark at the new history `new`. -/
theorem authHistOpen_freeze (γz : GName) (hs hs' new : List auth.AuthState) :
    ⊢ authHistOpen (GF := GF) γz hs -∗ dghostVar γz (.own (1 : Qp).half) (false, hs') ==∗
      ⌜hs = hs'⌝ ∗ authHistMark γz new := by
  unfold authHistOpen authHistMark
  iintro H1 H2
  ihave %Hag := dghostVar_agree γz _ _ _ _ $$ H1 H2
  imod (dghostVar_update_halves (true, new) γz _ _) $$ H1 H2 with ⟨H1, -⟩
  imod (dghostVar_persist γz _ _) $$ H1 with H1
  imodintro
  iframe H1
  ipureintro; exact (Prod.mk.inj Hag).2

theorem authHistOpen_mark (γz : GName) (hs hs' : List auth.AuthState) (dq : DFrac) :
    ⊢ dghostVar (GF := GF) γz dq (false, hs) -∗ authHistMark γz hs' -∗ False := by
  unfold authHistMark
  iintro H1 H2
  ihave %Hag := dghostVar_agree γz _ _ _ _ $$ H1 H2
  simp at Hag

theorem authHistMark_agree (γz : GName) (hs hs' : List auth.AuthState) :
    ⊢ authHistMark (GF := GF) γz hs -∗ authHistMark γz hs' -∗ ⌜hs = hs'⌝ := by
  unfold authHistMark
  iintro H1 H2
  ihave %Hag := dghostVar_agree γz _ _ _ _ $$ H1 H2
  ipureintro; exact (Prod.mk.inj Hag).2

/-- **A frozen history bounds every lower bound** (`↑authHistN ⊆ E`). -/
theorem authHistFrozen_prefix (γk : KVNames) (γz : GName) (hs hs' : List auth.AuthState)
    (E : CoPset) (hE : ↑authHistN ⊆ E) :
    ⊢ authHistFrozen (GF := GF) γk γz hs -∗ authHistLb γk hs' ={E}=∗ ⌜hs' <+: hs⌝ := by
  iintro #Hf #Hlb
  iunfold authHistFrozen at Hf
  icases Hf with ⟨#Hc, #Hm⟩
  iunfold authHistCell at Hc
  iinv Hc with >Hi Hclose
  icases Hi with ⟨%hs₀, Hv, Hz⟩
  ihave %Heq : ⌜hs₀ = hs⌝ $$ [Hz]
  · icases Hz with (Hz | #Hz)
    · iexfalso; iapply authHistOpen_mark γz hs₀ hs _ $$ Hz Hm
    · iapply authHistMark_agree γz hs₀ hs $$ Hz Hm
  subst Heq
  ihave %Hp := authHistView_prefix γk hs₀ hs' $$ [Hv Hlb]
  · iframe Hv Hlb
  imod Hclose $$ [Hv] with -
  · inext; iexists hs₀; iframe Hv; iright; iexact Hm
  imodintro
  ipureintro; exact Hp

/-- A frozen history is a lower bound of the history. -/
theorem authHistFrozen_lb (γk : KVNames) (γz : GName) (hs : List auth.AuthState)
    (E : CoPset) (hE : ↑authHistN ⊆ E) :
    ⊢ authHistFrozen (GF := GF) γk γz hs ={E}=∗ authHistLb γk hs := by
  iintro #Hf
  iunfold authHistFrozen at Hf
  icases Hf with ⟨#Hc, #Hm⟩
  iunfold authHistCell at Hc
  iinv Hc with >Hi Hclose
  icases Hi with ⟨%hs₀, Hv, Hz⟩
  ihave %Heq : ⌜hs₀ = hs⌝ $$ [Hz]
  · icases Hz with (Hz | #Hz)
    · iexfalso; iapply authHistOpen_mark γz hs₀ hs _ $$ Hz Hm
    · iapply authHistMark_agree γz hs₀ hs $$ Hz Hm
  subst Heq
  ihave #Hlb := authHistView_lb γk hs₀ $$ Hv
  imod Hclose $$ [Hv] with -
  · inext; iexists hs₀; iframe Hv; iright; iexact Hm
  imodintro
  iexact Hlb

/-- **A view is exclusive** (against the KV invariant's half, `↑kvN ⊆ E`). -/
theorem authHistView_excl (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (hs hs' : List auth.AuthState) (E : CoPset) (hE : ↑kvN ⊆ E) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ authHistView γk hs -∗ authHistView γk hs' ={E}=∗ False := by
  iintro #Hinv H1 H2
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw, HG⟩
  unfold authHistView at *
  ihave %Ha := monoListAuthOwn_agree γk.hist _ _ hs hs' $$ H1 H2
  ihave H12 := (monoListAuthOwn_fractional (GF := GF) γk.hist hs).fractional (1 : Qp).half
    (1 : Qp).half |>.2 $$ [H1 H2]
  · obtain ⟨-, rfl⟩ := Ha; iframe H1 H2
  rw [Qp.half_add_half]
  ihave %Hb := monoListAuthOwn_agree γk.hist _ _ hs _ $$ H12 Hh
  exact absurd Hb.1 (Qp_one_add_not_le _)

/-- **A lower bound of the requested log gives one of its history** (`↑kvN ⊆ E`). -/
theorem authHistLb_of_reqLogLb (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (L₀ : List EntryModel) (E : CoPset) (hE : ↑kvN ⊆ E) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ srvReqLogLb γ L₀ ={E}=∗
      authHistLb γk (admStates γk st₀ L₀) := by
  iintro #Hinv #H0
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw, HG⟩
  ihave ⟨HL, %Hp⟩ := srvReqLogLb_prefix γ L L₀ $$ [HL H0]
  · iframe HL H0
  ihave #Hlb := monoListLbOwn_get γk.hist _ _ $$ Hh
  imod Hclose $$ [HL Hσ Hh HG] with -
  · inext; iexists L; iframe HL Hσ Hh Hw HG; ipureintro; exact Hok
  imodintro
  unfold authHistLb admStates
  iapply (monoListLbOwn_le _ (admStatesR_prefix _ _ _ _ _ Hp))
  iexact Hlb

/-- The requested entries of the requested entries are themselves. -/
theorem opsOf_opsOf (a : List LogEntry) : opsOf (opsOf a) = opsOf a := by
  unfold opsOf; rw [List.filter_filter]; congr 1; funext e; simp [Bool.and_self]

/-- **The mode-`on` model of two logs with the same requested entries** is the same. -/
theorem kvRaftOfOn_eqv (γ : ServerRaftNames) (c₀ : w64) (ch : apply.Chain)
    (s : OnState) (A B : List EntryModel) (h : srvEqv γ A B)
    (hc : uint.Z c₀ ≤ uint.Z γ.ai0) : kvRaftOfOn c₀ ch s A = kvRaftOfOn c₀ ch s B := by
  obtain ⟨hA, hB, hops⟩ := h
  rw [kvRaftOfOn_ops c₀ ch A s (srvIdxOkW_above _ _ A hA hc),
    kvRaftOfOn_ops c₀ ch B s (srvIdxOkW_above _ _ B hB hc), hops]

/-- `admEntry` over a raft log entry (an entry above the start's index). -/
def admLE (st : auth.AuthState) (x : LogEntry) : Prop :=
  x.type = W32 0 ∧ x.data ≠ [] ∧ ∃ rq, apply.irrDecode x.data = some rq ∧
    adminDispatchKind (apply.dispatchKind rq) = true ∧
    auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))) ∧ adminNext rq st ≠ st

/-- `admStep` over raft log entries (`kvOpOn`'s). -/
noncomputable def admStepLE (ch : apply.Chain)
    (acc : OnState × List auth.AuthState) (x : LogEntry) :
    OnState × List auth.AuthState :=
  open Classical in
  (kvOpOn ch acc.1 x, if admLE acc.1.1 x then acc.2 ++ [(kvOpOn ch acc.1 x).1] else acc.2)

theorem admEntry_above (c₀ : w64) (st : auth.AuthState) (m : EntryModel)
    (h : uint.Z c₀ < uint.Z m.index) : admEntry c₀ st m ↔ admLE st m.toLE := by
  unfold admEntry admLE EntryModel.toLE
  constructor
  · rintro ⟨h1, h2, rq, h3, -, h4⟩; exact ⟨h1, h2, rq, h3, h4⟩
  · rintro ⟨h1, h2, rq, h3, h4⟩; exact ⟨h1, h2, rq, h3, h, h4⟩

theorem admStep_ops (c₀ : w64) (ch : apply.Chain) :
    ∀ (A : List EntryModel) (acc : OnState × List auth.AuthState),
      (∀ m ∈ A, uint.Z c₀ < uint.Z m.index) →
      A.foldl (admStep c₀ ch) acc = (opsOf (A.map EntryModel.toLE)).foldl (admStepLE ch) acc
  | [], _, _ => rfl
  | m :: A, acc, h => by
    have hA : ∀ m' ∈ A, uint.Z c₀ < uint.Z m'.index :=
      fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
    have hm := h m (List.mem_cons_self ..)
    rw [List.foldl_cons]
    by_cases hf : m.toLE.isFiller
    · have : opsOf ((m :: A).map EntryModel.toLE) = opsOf (A.map EntryModel.toLE) := by
        simp [opsOf, hf]
      rw [this]
      have hst : admStep c₀ ch acc m = acc := by
        have hna : ¬ admEntry c₀ acc.1.1 m := by
          obtain ⟨hd, -⟩ := hf
          simp only [EntryModel.toLE] at hd
          rintro ⟨-, h2, -⟩; exact h2 hd
        unfold admStep
        rw [kvEntryOn_filler c₀ ch acc.1 m hf]
        simp [hna]
      rw [hst]
      exact admStep_ops c₀ ch A acc hA
    by_cases hv : m.toLE.isEmptyV2
    · have : opsOf ((m :: A).map EntryModel.toLE) = opsOf (A.map EntryModel.toLE) := by
        simp [opsOf, hv]
      rw [this]
      have hst : admStep c₀ ch acc m = acc := by
        have hna : ¬ admEntry c₀ acc.1.1 m := by
          obtain ⟨-, ht⟩ := hv
          simp only [EntryModel.toLE] at ht
          rintro ⟨h1, -⟩; rw [ht] at h1; exact absurd h1 (by decide)
        unfold admStep
        rw [kvEntryOn_emptyV2 c₀ ch acc.1 m hv]
        simp [hna]
      rw [hst]
      exact admStep_ops c₀ ch A acc hA
    · have : opsOf ((m :: A).map EntryModel.toLE) =
          m.toLE :: opsOf (A.map EntryModel.toLE) := by
        simp [opsOf, hf, hv]
      rw [this, List.foldl_cons]
      have hst : admStep c₀ ch acc m = admStepLE ch acc m.toLE := by
        unfold admStep admStepLE
        rw [kvEntryOn_above c₀ ch acc.1 m hm]
        by_cases ha : admEntry c₀ acc.1.1 m
        · have hb := (admEntry_above c₀ acc.1.1 m hm).1 ha
          simp [ha, hb]
        · have hb : ¬ admLE acc.1.1 m.toLE := fun hb => ha ((admEntry_above c₀ acc.1.1 m hm).2 hb)
          simp [ha, hb]
      rw [hst]
      exact admStep_ops c₀ ch A _ hA

/-- **Logs with the same requested entries have the same auth history.** -/
theorem admStatesR_eqv (γ : ServerRaftNames) (c₀ : w64) (ch : apply.Chain)
    (s : OnState) (A B : List EntryModel) (h : srvEqv γ A B)
    (hc : uint.Z c₀ ≤ uint.Z γ.ai0) : admStatesR c₀ ch s A = admStatesR c₀ ch s B := by
  obtain ⟨hA, hB, hops⟩ := h
  unfold admStatesR
  rw [admStep_ops c₀ ch A _ (srvIdxOkW_above _ _ A hA hc),
    admStep_ops c₀ ch B _ (srvIdxOkW_above _ _ B hB hc), hops]

/-- **A lower bound's mode-`on` model is a prefix's** of the server's log of requested entries
(2026-10-27): the requested entries of a committed log `A` are a prefix of the server's `L`. -/
theorem kvRaftOfOn_of_lb (γ : ServerRaftNames) (c₀ : w64) (ch : apply.Chain)
    (s₀ : OnState) (A L : List EntryModel) (hc : uint.Z c₀ ≤ uint.Z γ.ai0)
    (hA : srvIdxOkW γ.ai0 A) (hL : srvIdxOkW γ.ai0 L) (hnf : ∀ m ∈ L, ¬ m.toLE.isFiller)
    (hp : opsOf (A.map EntryModel.toLE) <+: L.map EntryModel.toLE) :
    ∃ L', L' <+: L ∧ kvRaftOfOn c₀ ch s₀ A = kvRaftOfOn c₀ ch s₀ L' := by
  refine ⟨L.take (opsOf (A.map EntryModel.toLE)).length, List.take_prefix _ _, ?_⟩
  apply kvRaftOfOn_eqv γ c₀ ch s₀ _ _ ⟨hA, srvIdxOkW_prefix _ _ L hL (List.take_prefix _ _), ?_⟩ hc
  obtain ⟨r, hr⟩ := hp
  rw [List.map_take, ← hr, List.take_left' rfl, opsOf_opsOf]

/-- **Determinacy on a committed log** from the server's log of requested entries (2026-10-27): a
committed log's entries are the server's (at the same model state before them) or fillers (no
request, determinate). -/
theorem detLogOn_transfer (γ : ServerRaftNames) (c₀ : w64) (ch : apply.Chain)
    (s₀ : OnState) (B L : List EntryModel) (hc : uint.Z c₀ ≤ uint.Z γ.ai0)
    (hB : srvIdxOkW γ.ai0 B) (hL : srvIdxOkW γ.ai0 L) (hnf : ∀ m ∈ L, ¬ m.toLE.isFiller)
    (hp : opsOf (B.map EntryModel.toLE) <+: L.map EntryModel.toLE)
    (h : detLogOn c₀ ch s₀ L) : detLogOn c₀ ch s₀ B := by
  intro i m hm
  by_cases hf : m.toLE.isFiller
  · intro _ hd; exact absurd hf.1 hd
  by_cases hv : m.toLE.isEmptyV2
  · intro ht; obtain ⟨-, ht2⟩ := hv; simp only [EntryModel.toLE] at ht2
    rw [ht2] at ht; exact absurd ht (by decide)
  obtain ⟨m', hm', hme, htk⟩ := srv_pos B L i m hm ⟨hf, hv⟩ hp
  have hdet := h _ m' hm'
  have hBi : srvIdxOkW γ.ai0 (B.take i) := srvIdxOkW_prefix _ _ B hB (List.take_prefix _ _)
  have hLj : srvIdxOkW γ.ai0 (L.take (opsOf ((B.take i).map EntryModel.toLE)).length) :=
    srvIdxOkW_prefix _ _ L hL (List.take_prefix _ _)
  have hst : kvRaftOfOn c₀ ch s₀ (B.take i) =
      kvRaftOfOn c₀ ch s₀ (L.take (opsOf ((B.take i).map EntryModel.toLE)).length) := by
    apply kvRaftOfOn_eqv γ c₀ ch s₀ _ _ ⟨hBi, hLj, ?_⟩ hc
    rw [htk, opsOf_opsOf]
  rw [hst]
  have h1 := congrArg LogEntry.type hme
  have h2 := congrArg LogEntry.data hme
  simp only [EntryModel.toLE] at h1 h2
  intro ht hd rq hdec
  have hd' := hdet (h1 ▸ ht) (h2 ▸ hd) rq (h2 ▸ hdec)
  have hmi : uint.Z c₀ < uint.Z m.index := by
    obtain ⟨n, hn⟩ : ∃ n, B[n]? = some m := ⟨i, hm⟩
    have := (hB n m hn).1; omega
  have hm'i : uint.Z c₀ < uint.Z m'.index := by
    have := (hL _ m' hm').1; omega
  exact fun _ ha => hd' hm'i ha

/-- **The committed log is a mode-`on` log, determinate, and the start chain has auth on** (the
mode-`on` invariant's; `kv_log_plain`'s counterpart): what the apply thread reads of a committed
prefix `B` before applying its last entry. -/
theorem kv_log_plain_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (B : List EntryModel) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ srvRaftLogInv γ -∗ srvRLogLb γ B ={⊤}=∗
      ⌜plainLogOn γk.lm B ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0, []) B ∧
        γk.ch0 = apply.alarmChain true false false⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw, HG⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L B $$ Hr HL HB with ⟨HL, %Hp⟩
  ihave %HBi := srvRLogLb_idx γ B $$ HB
  imod Hclose $$ [HL Hσ Hh HG] with -
  · inext; iexists L; iframe HL Hσ Hh Hw HG; ipureintro; exact Hok
  imodintro
  ipureintro
  refine ⟨srv_entry_transfer γ.ai0 B L (plainEntryOn γk.lm) ?_ ?_ ?_ HBi Hp.2.2 Hok.1,
    detLogOn_transfer γ _ _ _ B L Hok.2.2.2.1 HBi Hp.1 (fun m hm => (Hp.2.1 m hm).1) Hp.2.2 Hok.2.1, Hok.2.2.2.2.1⟩
  · intro m m' he h ht hd rq hdec
    have h1 := congrArg LogEntry.type he
    have h2 := congrArg LogEntry.data he
    simp only [EntryModel.toLE] at h1 h2
    exact h (h1 ▸ ht) (h2 ▸ hd) rq (h2 ▸ hdec)
  · intro m _ hd _ h; exact absurd hd h
  · intro m ht _ h0; rw [ht] at h0; exact absurd h0 (by decide)

/-- **The mode-`on` KV invariant's start log attaches no key to a lease** (`kvInvOn`'s `LogNoLease γk.log0`,
the keys' invariants' base, auth-lease S3a). -/
theorem kvInvOn_log0 (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ ={⊤}=∗ ⌜mvcc.LogNoLease γk.log0⌝ := by
  iintro #Hinv
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw, HG⟩
  imod Hclose $$ [HL Hσ Hh HG] with -
  · inext; iexists L; iframe HL Hσ Hh Hw HG; ipureintro; exact Hok
  imodintro
  ipureintro; exact Hok.2.2.2.2.2.1.2

/-- **The keys' leases are live in the model of a committed log** (auth-lease S3a, Draft rev 5 §5:
`specSnapM`'s `hnl` at auth on). -/
theorem kvInvOn_keysLive (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (B : List EntryModel) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ ={⊤}=∗
      ⌜keysLeasesLive (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) B)⌝ := by
  iintro #Hinv
  imod (kvInvOn_log0 γ γk st₀) $$ Hinv with %h0
  imodintro; ipureintro
  exact keysLeasesLive_kvRaftOfOn _ _ _ _ B h0

end lemmas

end EtcdGrove
end Perennial
