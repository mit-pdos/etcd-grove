/-
**The apply thread's KV ghost state in the auth mode `on`** (the auth plan's E2t, 2026-10-26;
`notes/decisions.md`, "E2t of the auth plan"): `kv_applied_step`'s counterpart over E2q's mode-`on`
model (`KVAuthModel.lean`). The apply thread is at the committed raft log `A`, its auth state and KV
log the mode-`on` model of `A` (`kvAppliedOn`); the KV invariant `kvInvOn` keeps the committed log
a mode-`on` log, determinate (`detLogOn`), so the next entry `m` is admitted (`plainEntryOn`) and
determinate at the apply thread's state (`entryDetOn`), and the state after `m` is the model's
(`kvEntryOn`), whose log the apply thread certifies before applying `m` (`kv_cert_step_on`, at the
mode-`on` certificates' invariant `kvCertInvOn`).

What the apply thread does with `m` is the auth applier's (the auth plan's E2s): `outcomeOn` is the
relation its triples give (an admin entry: its step, the log kept; a KV entry the auth layer
refuses at the latest state: nothing; otherwise the entry's write), and at a determinate entry
every such outcome is the model's (`outcomeOn_eq`): the step's outcome is then the next state of
`kvAppliedOn` (`kv_applied_out_on`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

open Classical in
/-- **What the apply thread may make of entry `m` at the state `s`, in the mode `on`** (the
relation the auth applier's triples give, the auth plan's E2s): a normal entry with data that
decodes to `rq` is, if it needs the admin permission and its principal is not admin-permitted at
`s.1`, nothing (D1, 2026-11-27: `authApplierV3.Apply`'s refusal); above `c₀` and of a kind
`dispatch` applies as an admin step (`adminDispatchKind`), a successor of its admin step
(`adminStateR`), the log kept; a KV request the auth layer refuses at `s.1` (the latest state:
`auth.isOpPermitted.specL`, E2r), nothing; otherwise the entry's write at `s.1` (`kvEntry`). (Auth-lease
S3a: on the triple state, the guard `authKVKind` with the lease part, the write at the table.) -/
def outcomeOn (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel) (o : OnState) : Prop :=
  if m.typ = W32 0 ∧ m.data ≠ [] then
    match apply.irrDecode m.data with
    | some rq =>
      if apply.needAdminPermission rq = true ∧
          ¬ auth.adminOk s.1 (some (auth.authInfoM (apply.principalOf rq))) then o = s
      else if uint.Z c₀ < uint.Z m.index ∧ adminDispatchKind (apply.dispatchKind rq) = true then
        adminStateR rq s.1 o.1 ∧ o.2 = s.2
      else if apply.authKVKind (apply.dispatchKind rq) = true ∧
          ¬ kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq then o = s
      else o = (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)
    | none => o = s
  else o = (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)

/-- **At a determinate entry, every outcome the apply thread may reach is the model's**
(`kvEntryOn`): an admin entry's successor is the unique one (`adminNext_of_det`). -/
theorem outcomeOn_eq (c₀ : w64) (ch : apply.Chain) (s o : OnState)
    (m : EntryModel) (hd : entryDetOn c₀ s m) (ho : outcomeOn c₀ ch s m o) :
    o = kvEntryOn c₀ ch s m := by
  unfold outcomeOn at ho
  unfold kvEntryOn
  split
  · rename_i hm
    rw [if_pos hm] at ho
    split
    · rename_i rq hdec
      rw [hdec] at ho
      simp only at ho
      split
      · rename_i hrf
        rw [if_pos hrf] at ho; exact ho
      · rename_i hrf
        rw [if_neg hrf] at ho
        split
        · rename_i ha
          rw [if_pos ha] at ho
          have hdet := hd hm.1 hm.2 rq hdec ha.1
            (needAdminPermission_of_adminDispatchKind rq ha.2)
          obtain ⟨h1, h2⟩ := ho
          exact Prod.ext (adminNext_of_det rq s.1 o.1 hdet h1).symm h2
        · rename_i ha
          rw [if_neg ha] at ho
          split
          · rename_i hr; rw [if_pos hr] at ho; exact ho
          · rename_i hr; rw [if_neg hr] at ho; exact ho
    · rename_i hdec
      rw [hdec] at ho
      exact ho
  · rename_i hm
    rw [if_neg hm] at ho
    exact ho

/-- **The model's outcome is one the apply thread may reach** (`outcomeOn_eq`'s converse, at a
determinate entry): so `outcomeOn` at a determinate entry is exactly the model's step. -/
theorem outcomeOn_model (c₀ : w64) (ch : apply.Chain) (s : OnState)
    (m : EntryModel) (hd : entryDetOn c₀ s m) : outcomeOn c₀ ch s m (kvEntryOn c₀ ch s m) := by
  by_cases hm : m.typ = W32 0 ∧ m.data ≠ []
  · cases hdec : apply.irrDecode m.data with
    | none => simp only [outcomeOn, kvEntryOn, if_pos hm, hdec]
    | some rq =>
      by_cases hrf : apply.needAdminPermission rq = true ∧
          ¬ auth.adminOk s.1 (some (auth.authInfoM (apply.principalOf rq)))
      · simp only [outcomeOn, kvEntryOn, if_pos hm, hdec, if_pos hrf]
      by_cases ha : uint.Z c₀ < uint.Z m.index ∧ adminDispatchKind (apply.dispatchKind rq) = true
      · have hdet := hd hm.1 hm.2 rq hdec ha.1 (needAdminPermission_of_adminDispatchKind rq ha.2)
        simp only [outcomeOn, kvEntryOn, if_pos hm, hdec, if_neg hrf, if_pos ha]
        refine ⟨?_, trivial⟩
        simp only [adminNext, dif_pos hdet]
        exact (Classical.choose_spec hdet).1
      · by_cases hr : apply.authKVKind (apply.dispatchKind rq) = true ∧
            ¬ kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq
        · simp only [outcomeOn, kvEntryOn, if_pos hm, hdec, if_neg hrf, if_neg ha, if_pos hr]
        · simp only [outcomeOn, kvEntryOn, if_pos hm, hdec, if_neg hrf, if_neg ha, if_neg hr]
  · simp only [outcomeOn, kvEntryOn, if_neg hm]

open Classical in
/-- **`outcomeOn` of a request needing no admin permission**: the KV part (D1, 2026-11-27). -/
theorem outcomeOn_nonadmin (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel)
    (o : OnState) (rq : apply.IRRModel) (hm : m.typ = W32 0 ∧ m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hna : apply.needAdminPermission rq = false) :
    Iff (outcomeOn c₀ ch s m o)
      (if apply.authKVKind (apply.dispatchKind rq) = true ∧
          ¬ kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq then o = s
      else o = (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)) := by
  have hnk := adminDispatchKind_of_needAdmin_false rq hna
  unfold outcomeOn
  rw [if_pos hm, hdec]
  simp only [hna, hnk, Bool.false_eq_true, false_and, and_false, ↓reduceIte]

/-! ## The committer's side (the workload's and the proposers' obligation)

When raft's commit extends `kvInvOn`'s committed log `L` by `m`, the invariant asks `m` to be
admitted (`plainEntryOn`) and determinate at the model's state after `L` (`entryDetOn`):
`commitOkOn`, which the workload's entry claims and the proposers establish, as `plainEntry` today.
Then the log stays a mode-`on` log, determinate (`logOn_snoc`), and the client's update fires at
the model's new state: a granted write steps the KV state by its request (`kvModelOn_snoc_granted`),
an admin entry or a refused one keeps it (`kvModelOn_snoc_admin`, `kvModelOn_snoc_refused`). -/

/-- **What a newly committed entry `m` must be, after the committed log `L`, in the mode `on`**:
admitted and determinate at the model's state after `L`. -/
def commitOkOn (lm : lease.Mode) (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (L : List EntryModel) (m : EntryModel) : Prop :=
  plainEntryOn lm m ∧ entryDetOn c₀ (kvRaftOfOn c₀ ch s₀ L) m

/-- **The committed log stays a mode-`on` log, determinate**, extended by an entry meeting the
committer's obligation. -/
theorem logOn_snoc (lm : lease.Mode) (c₀ : w64) (ch : apply.Chain)
    (s₀ : OnState) (L : List EntryModel) (m : EntryModel)
    (hp : plainLogOn lm L) (hd : detLogOn c₀ ch s₀ L) (hc : commitOkOn lm c₀ ch s₀ L m) :
    plainLogOn lm (L ++ [m]) ∧ detLogOn c₀ ch s₀ (L ++ [m]) := by
  refine ⟨fun x hx => ?_, detLogOn_snoc c₀ ch s₀ L m hd hc.2⟩
  rcases List.mem_append.1 hx with h | h
  · exact hp x h
  · simp only [List.mem_singleton] at h; subst h; exact hc.1

/-- The auth layer does not change an entry's write (`chainLog`): the start's chain with auth on
writes as the one with auth off. -/
theorem kvEntry_alarmChain_on (c₀ : w64) (lt : LeaseTable) (log : mvcc.Log) (e : EntryModel) :
    kvEntry c₀ (apply.alarmChain true false false) lt log e =
      kvEntry c₀ (apply.alarmChain false false false) lt log e := by
  have hc : ∀ rq, chainLog (apply.alarmChain true false false) rq lt log =
      chainLog (apply.alarmChain false false false) rq lt log := by
    intro rq
    simp only [apply.alarmChain, apply.baseChain, Bool.false_eq_true, ↓reduceIte, chainLog]
  unfold kvEntry dispatchLog
  split
  · split
    · rfl
    · split
      · rename_i rq _; rw [hc rq]
      · rfl
  · rfl

/-- The auth layer does not change an entry's table either (`chainTable`). -/
theorem kvTable_alarmChain_on (c₀ : w64) (lt : LeaseTable) (e : EntryModel) :
    kvTable c₀ (apply.alarmChain true false false) lt e =
      kvTable c₀ (apply.alarmChain false false false) lt e := by
  have hc : ∀ rq, chainTable (apply.alarmChain true false false) rq lt =
      chainTable (apply.alarmChain false false false) rq lt := by
    intro rq
    simp only [apply.alarmChain, apply.baseChain, Bool.false_eq_true, ↓reduceIte, chainTable]
  unfold kvTable dispatchTable
  split
  · split
    · rfl
    · split
      · rename_i rq _; rw [hc rq]
      · rfl
  · rfl

/-- **The mode-`on` model of a log with short keys, from a start with none, has none**
(`kvRaftOf_keys`'s: an admin step and a refused request keep the log). -/
theorem kvRaftOfOn_keys (c₀ : w64) (ch : apply.Chain) :
    ∀ (s₀ : OnState) (A : List EntryModel), logPutsOk A →
      mvcc.LogPutsLe etcdKeyMax s₀.2.1 → mvcc.LogPutsLe etcdKeyMax (kvRaftOfOn c₀ ch s₀ A).2.1
  | s₀, [], _, hl => hl
  | s₀, m :: A, hA, hl => by
    have hk : kvRaftOfOn c₀ ch s₀ (m :: A) = kvRaftOfOn c₀ ch (kvEntryOn c₀ ch s₀ m) A := rfl
    rw [hk]
    apply kvRaftOfOn_keys c₀ ch _ A (fun m' h => hA m' (by simp [h]))
    have hm := hA m (by simp)
    unfold kvEntryOn
    split
    · split
      · split
        · exact hl
        · split
          · exact hl
          · split
            · exact hl
            · exact kvEntry_keys c₀ ch s₀.2.2 s₀.2.1 m hm hl
      · exact hl
    · exact kvEntry_keys c₀ ch s₀.2.2 s₀.2.1 m hm hl

end pure

section commit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- (2026-11-05, H-rr1) **The mode-`on` KV model of a small log has room** (`kvRoom_model`'s). -/
theorem kvRoom_modelOn (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) {lt : LeaseTable}
    (h : kvLogSmall γk L) : kvRoom (kvStateOf (kvModelOn γk st₀ L) lt) := by
  apply kvRoom_stateOf
  have := kvRaftOfOn_length_le γk.c0 γk.ch0 (st₀, γk.log0, []) L
  unfold kvModelOn; unfold kvLogSmall at h; simp only at this; omega

/-- The mode-`on` model after `L ++ [e]` is the step of `e` from the model after `L`. -/
theorem kvModelOn_snoc (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) :
    kvModelOn γk st₀ (L ++ [e]) =
      (kvEntryOn γk.c0 γk.ch0 (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L) e).2.1 := by
  unfold kvModelOn; rw [kvRaftOfOn_snoc]

/-- The mode-`on` table after `L ++ [e]` is the step of `e` from the model after `L`. -/
theorem kvLeasesOn_snoc (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) :
    kvLeasesOn γk st₀ (L ++ [e]) =
      (kvEntryOn γk.c0 γk.ch0 (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L) e).2.2 := by
  unfold kvLeasesOn; rw [kvRaftOfOn_snoc]

/-- **A granted entry steps the KV state by its request** (`kvModel_snoc_state`'s counterpart), at
the start's chain with auth on, above the consistent index: the auth state after `L` lets it through
(`kvGrantedL`, its lease part at the model's lease items, when the auth layer checks its kind).
(Auth-lease S3a: the state with the model's table, for every request kind.) -/
theorem kvModelOn_snoc_granted (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (hch : γk.ch0 = apply.alarmChain true false false)
    (h0 : γk.log0 ≠ []) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index)
    (hna : apply.needAdminPermission rq = false)
    (hg : apply.authKVKind (apply.dispatchKind rq) = true →
      kvGrantedL (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).1
        (mvcc.leaseItemsOf (mvcc.stateAfter (kvModelOn γk st₀ L))) rq) :
    kvStateOf (kvModelOn γk st₀ (L ++ [e])) (kvLeasesOn γk st₀ (L ++ [e])) =
      kvReqStep rq (kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)) := by
  rw [kvModelOn_snoc, kvLeasesOn_snoc, kvEntryOn_of_granted _ _ _ e rq hdec hna hg]
  have hm : (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).2.1 = kvModelOn γk st₀ L := rfl
  have hl : (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).2.2 = kvLeasesOn γk st₀ L := rfl
  simp only
  rw [hm, hl, hch, kvEntry_alarmChain_on, kvTable_alarmChain_on,
    kvEntry_base γk.c0 _ _ e rq ht hd hdec hidx, kvTable_base γk.c0 _ e rq ht hd hdec hidx]
  rw [kvStateOf_backendLog _ rq _ ?_]
  intro he
  apply h0
  have hp := kvRaftOfOn_extends γk.c0 γk.ch0 (st₀, γk.log0, []) L
  unfold kvModelOn at he
  rw [he] at hp
  exact List.prefix_nil.1 hp

/-- **An admin entry keeps the KV log** (the auth state steps, `kvEntryOn_admin`). -/
theorem kvModelOn_snoc_admin (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index)
    (ha : adminDispatchKind (apply.dispatchKind rq) = true) :
    kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L := by
  rw [kvModelOn_snoc, kvEntryOn_admin _ _ _ e rq ht hd hdec hidx ha]
  rfl

/-- **An admin entry keeps the table.** -/
theorem kvLeasesOn_snoc_admin (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index)
    (ha : adminDispatchKind (apply.dispatchKind rq) = true) :
    kvLeasesOn γk st₀ (L ++ [e]) = kvLeasesOn γk st₀ L := by
  rw [kvLeasesOn_snoc, kvEntryOn_admin _ _ _ e rq ht hd hdec hidx ha]
  rfl

/-- **A request the auth state after `L` refuses keeps the model's state.** -/
theorem kvRaftOfOn_snoc_refused (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hna : apply.needAdminPermission rq = false)
    (hk : apply.authKVKind (apply.dispatchKind rq) = true)
    (hr : ¬ kvGrantedL (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).1
      (mvcc.leaseItemsOf (mvcc.stateAfter (kvModelOn γk st₀ L))) rq) :
    kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) (L ++ [e]) =
      kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L := by
  rw [kvRaftOfOn_snoc, kvEntryOn_of_refused _ _ _ e rq ht hd hdec hna hk hr]

/-- **A request the auth state after `L` refuses keeps the KV log.** -/
theorem kvModelOn_snoc_refused (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hna : apply.needAdminPermission rq = false)
    (hk : apply.authKVKind (apply.dispatchKind rq) = true)
    (hr : ¬ kvGrantedL (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).1
      (mvcc.leaseItemsOf (mvcc.stateAfter (kvModelOn γk st₀ L))) rq) :
    kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L := by
  unfold kvModelOn; rw [kvRaftOfOn_snoc_refused γk st₀ L e rq ht hd hdec hna hk hr]

/-- **A request the auth state after `L` refuses keeps the table.** -/
theorem kvLeasesOn_snoc_refused (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hna : apply.needAdminPermission rq = false)
    (hk : apply.authKVKind (apply.dispatchKind rq) = true)
    (hr : ¬ kvGrantedL (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) L).1
      (mvcc.leaseItemsOf (mvcc.stateAfter (kvModelOn γk st₀ L))) rq) :
    kvLeasesOn γk st₀ (L ++ [e]) = kvLeasesOn γk st₀ L := by
  unfold kvLeasesOn; rw [kvRaftOfOn_snoc_refused γk st₀ L e rq ht hd hdec hna hk hr]

end commit

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The certificates' map `C` in the mode `on` (`certMapOk`'s, with the mode-`on` model from the
start's auth state `st₀`). -/
def certMapOkOn (γk : KVNames) (st₀ : auth.AuthState) (C : GMap w64 mvcc.Log) (hi : Nat)
    (Lb : List EntryModel) : Prop :=
  ∀ n l, C.lookup n = some l → l.length ≤ hi ∧ n = W64 (l.length : Int) ∧ l.length < 2 ^ 63 ∧
    ∃ A, A <+: Lb ∧ kvModelOn γk st₀ A = l

/-- **The certificates' invariant in the mode `on`** (`kvCertInv`'s, over `certMapOkOn`). -/
def kvCertInvOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) : IProp GF :=
  inv kvcN iprop(∃ (C : GMap w64 mvcc.Log) (hi : Nat) (Lb : List EntryModel),
    ghostMapAuth γk.cok 1 C ∗ ghostVar γk.hi (1 : Qp).half hi ∗ srvRLogLb γ Lb ∗
    ⌜certMapOkOn γk st₀ C hi Lb ∧ 2 ≤ γk.log0.length⌝)

instance kvCertInvOn_persistent (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    Persistent (kvCertInvOn (GF := GF) γ γk st₀) := by
  unfold kvCertInvOn; infer_instance

/-- **The apply thread's KV ghost state in the mode `on`** at the applied raft log `A` and its auth
state and KV log `s`: `A` committed, `s` its mode-`on` model, the log certified, the longest
certified length (`kvAppliedL`'s). -/
def kvAppliedLOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (s : OnState) : IProp GF :=
  iprop(srvRLogLb γ A ∗ ghostVar γk.hi (1 : Qp).half s.2.1.length ∗ kvCert γk s.2.1 ∗
    ⌜s = kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) A⌝)

/-- `kvAppliedLOn` of the apply thread's state `x`, its latest auth state `st` and the model's lease
table `lt` (auth-lease S3a), at the start's chain (`kvApplied`'s). -/
def kvAppliedOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (x : apply.ApplyKV) (st : auth.AuthState) (lt : LeaseTable) : IProp GF :=
  iprop(kvAppliedLOn γ γk st₀ A (st, x.log, lt) ∗ ⌜x.chain = γk.ch0⌝)

/-- The namespace of the server's tie of the auth store's history to the log (H5). -/
def authTieN : Namespace := nroot .@ "auth_tie"

/-- **The auth store's history tied to the log** (H5, 2026-10-29; persistent): in the mode
`on γa`, the store's invariant (`auth.authInv`, which keeps its history below the cap,
`auth.authOwn_capped`), and an invariant holding the cap's authority (`auth.capAuth`) at the
history some committed log `A` records (the boot state, then `admStates` from `st₀`): the store's
history is always a prefix of a history of the committed log, and the apply thread raises the cap
by the entry it applies (`authHistTie_raise`). `True` in the other modes. -/
def authHistTie (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) : IProp GF :=
  match E.authMode with
  | .on γa => iprop((∃ (stl : Loc) (R : IProp GF), auth.authInv stl R (.on γa)) ∗
      inv authTieN iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗
        auth.capAuth γa (auth.bootState :: admStates γr.kv st₀ A)))
  | _ => iprop(True)

instance authHistTie_persistent (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) :
    Persistent (authHistTie (GF := GF) E γr st₀) := by
  unfold authHistTie; split <;> infer_instance

/-- **The log `l` is the mode-`on` model, from `st₀`, of a committed raft log** (persistent; strict
M1, 2026-11-06: `kvNxOff`'s; `KVStoreApi.lean`'s `kvNx γr true` at `st₀ = srvAuthSt0`, by `rfl`). -/
def kvNxOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (l : mvcc.Log) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗ ⌜kvModelOn γk st₀ A = l ∧ mvcc.LogPutsLe etcdKeyMax l⌝)

instance kvNxOn_persistent (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (l : mvcc.Log) : Persistent (kvNxOn (GF := GF) γ γk st₀ l) := by
  unfold kvNxOn; infer_instance

/-- **The apply thread's KV invariants in the mode `on`** (`srvKVInvs`'s); (H5) with the auth
store's history's tie to the log (`authHistTie`). (Strict M1, 2026-11-06, as
`srvKVInvs`: the tie `E.γ.cok = γr.kv.cok` and mvcc's permit invariant `crevPermIs` gone, the store
invariant `kvStoreInvG` at the chain's witness and permit, boxed, with `envWitOk`, in their place; the
witness tied to the mode's model, `kvNxOn`, as `srvKVInvs`' to `kvNxOff`. Merge of `lean`,
2026-11-06: #7-on's `E.cmp = false` dropped, the API's image covering a compacting store; restored
by R6, 2026-11-07, as `γr.kv.cmp = false`, `lean`'s scope restriction, dropped by accident: the
on-mode image certificate is at `crevOf γr.kv A`, `-1`, which the apply thread's compaction
revision meets only when the cluster never compacts, `kvCpOk`.) (Auth-lease S3a, Draft rev 5 §3: the model's lease mode the
environment's, `γr.kv.lm = E.lm`, and the raft prefix empty, `γr.raft.pre = []`, so the model's table and
`srvRest`'s agree, `appliedTableM_eq_model`. From the lease-grant merge, 2026-11-03, until S3a's §6 also
`γr.kv.lg = false`, a cluster that grants no lease: dropped once the apply thread's grant and revocation arms
were proved.) (Auth-lease S4 item 7b F4, last conjunct) The lessor-window tie, as `srvKVInvs`'. -/
def srvKVInvsOn (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) : IProp GF :=
  iprop(kvInvOn γr.raft γr.kv st₀ ∗ kvCertInvOn γr.raft γr.kv st₀ ∗ srvRaftLogInv γr.raft ∗
    authHistTie E γr st₀ ∗ □ srvApi.kvStoreInvG E.kv E.γ E.Nx E.Cp E.γs ∗
    ⌜envWitOk E ∧ E.Cp = kvCpOk γr.kv⌝ ∗
    ⌜E.Nx = kvNxOn γr.raft γr.kv st₀⌝ ∗
    ⌜γr.kv.cmp = false ∧ γr.kv.lm = E.lm ∧ γr.raft.pre = []⌝ ∗
    srvApi.winTieRes E (clusterNoSnap γr.raft.raft.cl → E.lg = false))

instance srvKVInvsOn_persistent (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) :
    Persistent (srvKVInvsOn (GF := GF) E γr st₀) := by
  unfold srvKVInvsOn; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The apply thread certifies the mode-`on` model's log after the next committed entry**
(`kv_cert_step`'s counterpart). -/
theorem kv_cert_step_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (E : CoPset)
    (hE : ↑kvcN ⊆ E) (A : List EntryModel) (m : EntryModel) (s s' : OnState)
    (hs' : s' = kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0, []) (A ++ [m]))
    (hg : s'.2.1 = s.2.1 ∨ ∃ cs, s'.2.1 = s.2.1 ++ [cs]) (hlen : s'.2.1.length < 2 ^ 63) :
    ⊢ kvCertInvOn (GF := GF) γ γk st₀ -∗ kvAppliedLOn γ γk st₀ A s -∗ srvRLogLb γ (A ++ [m]) ={E}=∗
      kvAppliedLOn γ γk st₀ (A ++ [m]) s' := by
  iintro #Hinv Ha #Hlb
  iunfold kvAppliedLOn at Ha
  icases Ha with ⟨#HA, Hhi, #Hc, %Hl⟩
  have hm' : kvModelOn γk st₀ (A ++ [m]) = s'.2.1 := by unfold kvModelOn; rw [hs']
  rcases hg with hg | ⟨cs, hg⟩
  · imodintro
    iunfold kvAppliedLOn
    rw [hg]
    iframe Hlb Hhi Hc
    ipureintro; exact hs'
  · iunfold kvCertInvOn at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hhe := ghostVar_agree γk.hi _ _ _ _ $$ Hhi Hhi'
    rw [hg] at hlen hm'
    have hfresh : C.lookup (W64 ((s.2.1 ++ [cs]).length : Int)) = none := by
      cases h : C.lookup (W64 ((s.2.1 ++ [cs]).length : Int)) with
      | none => rfl
      | some l'' =>
        obtain ⟨h1, h2, h3, -⟩ := Hok.1 _ _ h
        have := w64_len_inj _ _ hlen h3 h2
        simp only [List.length_append, List.length_singleton] at this
        omega
    imod ghost_map_insert_persist _ (s.2.1 ++ [cs]) hfresh $$ HC with ⟨HC, #He⟩
    imod ghostVar_update_halves (s.2.1 ++ [cs]).length γk.hi _ _ $$ Hhi Hhi' with ⟨Hhi, Hhi'⟩
    ihave %Hcmp := srvRLogLb_prefix γ (A ++ [m]) Lb $$ [Hlb HLb]
    · iframe Hlb HLb
    have hold : ∀ n l2, C.lookup n = some l2 → l2.length ≤ (s.2.1 ++ [cs]).length := by
      intro n l2 hn
      have := (Hok.1 n l2 hn).1
      simp only [List.length_append, List.length_singleton]
      omega
    imod Hclose $$ [HC Hhi'] with -
    · inext
      rcases Hcmp with h | h
      · iexists C.insert (W64 ((s.2.1 ++ [cs]).length : Int)) (s.2.1 ++ [cs]), (s.2.1 ++ [cs]).length, Lb
        iframe HC Hhi' HLb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A ++ [m], h, hm'⟩
        · obtain ⟨-, h2, h3, A', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A', h4, h5⟩
      · iexists C.insert (W64 ((s.2.1 ++ [cs]).length : Int)) (s.2.1 ++ [cs]), (s.2.1 ++ [cs]).length,
          A ++ [m]
        iframe HC Hhi' Hlb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A ++ [m], List.prefix_refl _, hm'⟩
        · obtain ⟨-, h2, h3, A', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A', h4.trans h, h5⟩
    imodintro
    iunfold kvAppliedLOn
    rw [hg]
    iframe Hlb Hhi
    isplitr
    · iunfold kvCert; iright; iexact He
    ipureintro; exact hs'

/-- **The apply thread's step on the next committed entry `m`, in the mode `on`**
(`kv_applied_step`'s counterpart): `m` admitted (`plainEntryOn`) and determinate at the apply
thread's state (`entryDetOn`), the chain the start's (auth on), and the state after `m` the
model's (`kvEntryOn`), certified. -/
theorem kv_applied_step_on (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (m : EntryModel) (x : apply.ApplyKV) (st : auth.AuthState)
    (lt : LeaseTable)
    (hlen : (kvEntryOn γr.kv.c0 x.chain (st, x.log, lt) m).2.1.length < 2 ^ 63) :
    ⊢ srvKVInvsOn (GF := GF) E γr st₀ -∗ kvAppliedOn γr.raft γr.kv st₀ A x st lt -∗
      srvRLogLb γr.raft (A ++ [m]) ={⊤}=∗
      ⌜plainEntryOn γr.kv.lm m ∧ entryDetOn γr.kv.c0 (st, x.log, lt) m ∧ x.chain = γr.kv.ch0 ∧
        x.chain = apply.alarmChain true false false⌝ ∗
      kvAppliedLOn γr.raft γr.kv st₀ (A ++ [m]) (kvEntryOn γr.kv.c0 x.chain (st, x.log, lt) m) := by
  iintro #Hinvs Ha #Hlb
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, -, -, -⟩
  iunfold kvAppliedOn at Ha
  icases Ha with ⟨Ha, %Hch⟩
  imod kv_log_plain_on γr.raft γr.kv st₀ (A ++ [m]) $$ HkI HrI Hlb with %Hpc
  obtain ⟨Hpl, Hdet, Hch0⟩ := Hpc
  ihave %Hl : iprop(⌜(st, x.log, lt) = kvRaftOfOn γr.kv.c0 γr.kv.ch0 (st₀, γr.kv.log0, []) A⌝) $$ [Ha]
  · iunfold kvAppliedLOn at Ha; icases Ha with ⟨-, -, -, %h⟩; ipureintro; exact h
  have hs' : kvEntryOn γr.kv.c0 x.chain (st, x.log, lt) m =
      kvRaftOfOn γr.kv.c0 γr.kv.ch0 (st₀, γr.kv.log0, []) (A ++ [m]) := by
    rw [kvRaftOfOn_snoc, ← Hl, Hch]
  have hd : entryDetOn γr.kv.c0 (st, x.log, lt) m := by
    have h := Hdet A.length m (by simp)
    rw [List.take_left' rfl, ← Hl] at h
    exact h
  imod kv_cert_step_on γr.raft γr.kv st₀ ⊤ (fun _ _ => CoPset.mem_full) A m (st, x.log, lt) _ hs'
    (kvEntryOn_grow γr.kv.c0 x.chain (st, x.log, lt) m) hlen $$ HcI Ha Hlb with Ha
  imodintro
  iframe Ha
  ipureintro
  exact ⟨Hpl m (by simp), hd, Hch, Hch.trans Hch0⟩

/-- **The apply thread's outcome is the model's** (`kv_applied_step_on` with the auth applier's
outcome, E2s): any outcome `o` the apply thread reaches on `m` (`outcomeOn`) is the next state of
`kvAppliedLOn`. -/
theorem kv_applied_out_on (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (m : EntryModel) (x : apply.ApplyKV) (st : auth.AuthState)
    (lt : LeaseTable) (o : OnState)
    (hlen : (kvEntryOn γr.kv.c0 x.chain (st, x.log, lt) m).2.1.length < 2 ^ 63)
    (hout : entryDetOn γr.kv.c0 (st, x.log, lt) m →
      outcomeOn γr.kv.c0 x.chain (st, x.log, lt) m o) :
    ⊢ srvKVInvsOn (GF := GF) E γr st₀ -∗ kvAppliedOn γr.raft γr.kv st₀ A x st lt -∗
      srvRLogLb γr.raft (A ++ [m]) ={⊤}=∗
      ⌜plainEntryOn γr.kv.lm m ∧ x.chain = apply.alarmChain true false false⌝ ∗
      kvAppliedLOn γr.raft γr.kv st₀ (A ++ [m]) o := by
  iintro #Hinvs Ha #Hlb
  imod kv_applied_step_on E γr st₀ A m x st lt hlen $$ Hinvs Ha Hlb with ⟨%Hp, Ha⟩
  obtain ⟨Hpl, hd, -, hch⟩ := Hp
  have ho := hout hd
  rw [outcomeOn_eq γr.kv.c0 x.chain (st, x.log, lt) o m hd ho]
  imodintro
  iframe Ha
  ipureintro
  exact ⟨Hpl, hch⟩

/-- **A committed raft prefix's model has short keys** (R8, 2026-11-07: what the store's witness's
producers prove its key bound with): the KV invariant keeps its work log's entries short
(`kvWork`'s `logPutsOk`, from the start log's). -/
theorem kvInv_keysA (γr : ReadNames) (A : List EntryModel) :
    ⊢ kvInv (GF := GF) γr.raft γr.kv -∗ srvRaftLogInv γr.raft -∗ srvRLogLb γr.raft A ={⊤}=∗
      ⌜mvcc.LogPutsLe etcdKeyMax (kvModel γr.kv A)⌝ := by
  iintro #HkI #HrI #HA
  iunfold kvInv at HkI
  iinv HkI with >Hi Hclose
  icases Hi with ⟨%Lf, HLf, Hσ', %Hok', #Hw, HG⟩
  ihave #Hw2 := Hw
  iunfold kvWork at Hw2
  icases Hw2 with ⟨%Hws, -⟩
  imod srvRLog_lb γr.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    Lf A $$ HrI HLf HA with ⟨HLf, %Hp⟩
  ihave %HAi := srvRLogLb_idx γr.raft A $$ HA
  imod Hclose $$ [HLf Hσ' HG] with -
  · inext; iexists Lf; iframe HLf Hσ' Hw HG; ipureintro; exact Hok'
  imodintro
  ipureintro
  obtain ⟨A', hA'L, hA'⟩ := srv_eqv_prefix γr.raft A Lf HAi Hp.1 Hp.2.1 Hp.2.2
  rw [(kvModel_eqv γr.raft γr.kv A A' hA' Hok'.2.2.1).1]
  rw [kvModel_offM _ A' (fun m hm => Hok'.1 m (hA'L.subset hm))]
  exact kvRaftOf_keys _ _ _ A' (fun m hm => Hws.2.2.1 m (hA'L.subset hm)) Hws.2.2.2.1

/-- `kvInv_keysA` in the mode `on`, at the start's auth state `st₀`. -/
theorem kvInvOn_keysA (γr : ReadNames) (st₀ : auth.AuthState) (A : List EntryModel) :
    ⊢ kvInvOn (GF := GF) γr.raft γr.kv st₀ -∗ srvRaftLogInv γr.raft -∗ srvRLogLb γr.raft A ={⊤}=∗
      ⌜mvcc.LogPutsLe etcdKeyMax (kvModelOn γr.kv st₀ A)⌝ := by
  iintro #HkI #HrI #HA
  iunfold kvInvOn at HkI
  iinv HkI with >Hi Hclose
  icases Hi with ⟨%Lf, HLf, Hσ', Hh, %Hok', #Hw, HG⟩
  ihave #Hw2 := Hw
  iunfold kvWorkOn at Hw2
  icases Hw2 with ⟨%Hws, -⟩
  imod srvRLog_lb γr.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    Lf A $$ HrI HLf HA with ⟨HLf, %Hp⟩
  ihave %HAi := srvRLogLb_idx γr.raft A $$ HA
  imod Hclose $$ [HLf Hσ' Hh HG] with -
  · inext; iexists Lf; iframe HLf Hσ' Hh Hw HG; ipureintro; exact Hok'
  imodintro
  ipureintro
  obtain ⟨L', hL', hAL⟩ := kvRaftOfOn_of_lb γr.raft γr.kv.c0 γr.kv.ch0
    (st₀, γr.kv.log0, []) A Lf Hok'.2.2.2.1 HAi Hp.1 (fun m hm => (Hp.2.1 m hm).1) Hp.2.2
  unfold kvModelOn
  rw [hAL]
  exact kvRaftOfOn_keys _ _ _ L' (fun m hm => Hws.2.2.1 m (hL'.subset hm)) Hws.2.2.2.1

end lemmas

end EtcdGrove
end Perennial
