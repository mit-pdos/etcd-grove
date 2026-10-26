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
  grants its principal every permission the request needs (`kvGranted`: auth disabled, or a
  revision that is not `0` and not below the store's -- `ErrAuthOldRevision` -- and a user with the
  root role or whose permissions cover each of `reqPerms`); otherwise it is refused and leaves the
  log alone.
- Every other entry is today's (`kvEntry`).

**Why a function of the committed log, and why determinacy is a premise of the log.** The KV
invariant ties the KV state (`etcdKV`'s ghost variable) to the model of raft's *committed* log
(`srvRLog`), and a client's update fires when its entry commits (`kvAu`), before any member applies
it. So the model must be a function of the committed log; recording the auth state per entry in
ghost state (E2p's other option) would make the committer, raft's commit, choose an outcome the
apply thread must later reproduce, which only works if the outcome is a function of the prefix. In
Go it is (every member applies the same prefix), but three of the model's admin steps are relations
(`userGrantRoleR`, `roleGrantPermissionR`: the record's order after `sort.Sort`, a permission of an
unknown type; `UserAdd`'s `ErrNoPasswordUser`, a refusal decided by the request's password choice,
which the request model keeps since E2t: `UserAddModel.pwSure` rules it out), so the model's step is the *unique* successor where there is one (`adminNext`), and the
mode-`on` log premise (`detLogOn`) asks every committed admin entry to have a unique successor at
the state it is applied at, and every KV entry with auth enabled to be of the shape the permission
cache decides (`kvDet`: `auth.reqShape`, outside of which the cache's answer is not stated). Both
are the workload's to establish, as `plainLog` is today. The apply thread's actual outcome is then
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
public import Proof.go_etcd_io.etcd.server.v3.auth.Steps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [ext : FfiSyntax]

/-! ## The admin entries' step -/

/-- The state after an admin operation's outcome at `st`: a refusal and nothing to do leave it,
`next` replaces it. -/
def outState (st : auth.AuthState) : auth.Outcome → auth.AuthState
  | .err _ => st
  | .same => st
  | .next st' => st'

/-- A step relation's successors of `st`, as states. -/
def relState (R : auth.StepRel) (st st' : auth.AuthState) : Prop :=
  ∃ o, R st o ∧ st' = outState st o

open Classical in
/-- **An admitted admin entry's effect on the auth state** (`st` to `st'`): with the principal
admin-permitted at `st` (`auth.adminOk`; `authApplierV3.Apply` checks it of `needAdminPermission`
requests), its kind's step (`auth/Steps.lean`; the flag the steps read is `st`'s: the apply thread
applies at the latest state); otherwise nothing. `UserAdd` may also be refused with
`ErrNoPasswordUser` (the state kept), unless its password choice cannot fail
(`UserAddModel.pwSure`, the auth plan's E2t: the request model keeps it). An entry of another
kind keeps the state (the mode-`on` log admits none: `plainEntryOn`). -/
def adminStateR (rq : apply.IRRModel) (st st' : auth.AuthState) : Prop :=
  if auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))) then
    match apply.dispatchKind rq with
    | .authUserAdd =>
        match rq.authUserAdd with
        | some m => (¬ m.pwSure ∧ st' = st) ∨ relState (auth.stepOf (auth.userAddF m.name)) st st'
        | none => st' = st
    | .authRoleAdd =>
        match rq.authRoleAdd with
        | some n => relState (auth.stepOf (auth.roleAddF n)) st st'
        | none => st' = st
    | .authUserGrantRole =>
        match rq.authUserGrantRole with
        | some (u, r) => relState (auth.userGrantRoleR u r) st st'
        | none => st' = st
    | .authRoleGrantPermission =>
        match rq.authRoleGrantPermission with
        | some (r, w) => relState (auth.roleGrantPermissionR r w) st st'
        | none => st' = st
    | .authEnable => relState (auth.stepOf (auth.authEnableF st.enabled)) st st'
    | _ => st' = st
  else st' = st

/-- **The admin entry is determinate at `st`**: one successor state. -/
def authDet (rq : apply.IRRModel) (st : auth.AuthState) : Prop :=
  ∃ st', adminStateR rq st st' ∧ ∀ st'', adminStateR rq st st'' → st'' = st'

open Classical in
/-- **The model's admin step**: the unique successor, where there is one (else the state kept; a
committed entry always has one, `detLogOn`). -/
def adminNext (rq : apply.IRRModel) (st : auth.AuthState) : auth.AuthState :=
  if h : authDet rq st then Classical.choose h else st

/-- **The apply thread's admin outcome is the model's**: any successor the step allows is the
model's, at a determinate entry. -/
theorem adminNext_of_det (rq : apply.IRRModel) (st st' : auth.AuthState) (hd : authDet rq st)
    (h : adminStateR rq st st') : adminNext rq st = st' := by
  unfold adminNext
  rw [dif_pos hd]
  have hc := Classical.choose_spec hd
  exact ((hc.2 st' h).trans (hc.2 _ hc.1).symm).symm

/-! ## The KV entries' check -/

mutual
/-- The permissions a transaction's operation needs (`checkTxnReqsPermission`'s walk, `opClass`):
a get's read, a put's write of its key, a delete's write and `PrevKv` read, a nested transaction's
comparisons and both branches. -/
def opPerms : TxnOp → List apply.Perm3
  | .get o => [(o.key, o.base.rangeEnd, .read)]
  | .put k _ _ => [(k, [], .write)]
  | .putKeep k _ => [(k, [], .write)]
  | .putIgnVal k _ => [(k, [], .write)]
  | .delete o => (o.key, o.base.rangeEnd, .write) ::
      if o.base.prevKV then [(o.key, o.base.rangeEnd, .read)] else []
  | .txn cs ts es => cs.map (fun cm => (cm.key, cm.rangeEnd, .read)) ++ opsPerms ts ++ opsPerms es

/-- The permissions a list of operations needs, in order. -/
def opsPerms : List TxnOp → List apply.Perm3
  | [] => []
  | op :: ops => opPerms op ++ opsPerms ops
end

/-- **The permissions a KV request needs** (`apply.reqClass`, purely): a put's (`apply.putPerms`),
a delete's write and `PrevKv` read of its range, a range's read, a transaction's comparisons'
reads and both branches' operations. -/
def reqPerms (rq : apply.IRRModel) : List apply.Perm3 :=
  match apply.dispatchKind rq with
  | .put => match rq.put with
      | some o => apply.putPerms o
      | none => []
  | .deleteRange => match rq.deleteRange with
      | some o => (o.key, o.base.rangeEnd, .write) ::
          if o.base.prevKV then [(o.key, o.base.rangeEnd, .read)] else []
      | none => []
  | .range => match rq.range with
      | some o => [(o.key, o.base.rangeEnd, .read)]
      | none => []
  | .txn => match rq.txn with
      | some t => t.cmps.map (fun cm => (cm.key, cm.rangeEnd, .read)) ++ opsPerms t.thenOps ++
          opsPerms t.elseOps
      | none => []
  | _ => []

/-- **The auth layer lets the KV request `rq` through at `st`** (`isOpPermitted` for each of its
permissions, at one state: the apply thread is the store's only writer): auth disabled, or the
principal's revision not `0` (`ErrUserEmpty`) and not below the store's (`ErrAuthOldRevision`), and
its user existing with the root role or with permissions covering each permission the request
needs. -/
def kvGranted (st : auth.AuthState) (rq : apply.IRRModel) : Prop :=
  st.enabled = false ∨
    ((auth.authInfoM (apply.principalOf rq)).rev ≠ 0 ∧
      st.revision ≤ (auth.authInfoM (apply.principalOf rq)).rev ∧
      ∃ u, st.users !! (auth.authInfoM (apply.principalOf rq)).user = some u ∧
        (auth.isRoot u ∨ ∀ x ∈ reqPerms rq, auth.covers st u x.2.2 x.1 x.2.1))

/-- **The check is decided at `st`**: with auth enabled, every permission the request needs is of
the shape the permission cache decides (`auth.reqShape`). -/
def kvDet (st : auth.AuthState) (rq : apply.IRRModel) : Prop :=
  st.enabled = true → ∀ x ∈ reqPerms rq, auth.reqShape x.1 x.2.1

/-! ## The model -/

open Classical in
/-- **An entry's effect in the mode `on`**, from the consistent index `c₀` with the chain `ch`, on
the auth state and the KV log `s`: a normal entry with data that decodes to `rq` is, above `c₀`
(`v3`) and of an admin kind, the admin step (the log kept); a KV request the auth layer refuses at
`s.1`, nothing; otherwise today's `kvEntry`. -/
def kvEntryOn (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log) (m : EntryModel) :
    auth.AuthState × mvcc.Log :=
  if m.typ = W32 0 ∧ m.data ≠ [] then
    match apply.irrDecode m.data with
    | some rq =>
      if uint.Z c₀ < uint.Z m.index ∧ apply.needAdminPermission rq = true then
        (adminNext rq s.1, s.2)
      else if apply.isKVKind (apply.dispatchKind rq) = true ∧ ¬ kvGranted s.1 rq then s
      else (s.1, kvEntry c₀ ch s.2 m)
    | none => s
  else (s.1, kvEntry c₀ ch s.2 m)

/-- **The mode-`on` model of a raft log** `A`, from the start's auth state and log `s₀`. -/
def kvRaftOfOn (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (A : List EntryModel) : auth.AuthState × mvcc.Log :=
  A.foldl (kvEntryOn c₀ ch) s₀

theorem kvRaftOfOn_nil (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log) :
    kvRaftOfOn c₀ ch s₀ [] = s₀ := rfl

theorem kvRaftOfOn_append (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (A B : List EntryModel) :
    kvRaftOfOn c₀ ch s₀ (A ++ B) = kvRaftOfOn c₀ ch (kvRaftOfOn c₀ ch s₀ A) B := by
  unfold kvRaftOfOn; exact List.foldl_append

theorem kvRaftOfOn_snoc (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (A : List EntryModel) (m : EntryModel) :
    kvRaftOfOn c₀ ch s₀ (A ++ [m]) = kvEntryOn c₀ ch (kvRaftOfOn c₀ ch s₀ A) m := by
  rw [kvRaftOfOn_append]; rfl

/-- **An admin entry above `c₀` steps the auth state and keeps the log.** -/
theorem kvEntryOn_admin (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (ha : apply.needAdminPermission rq = true) :
    kvEntryOn c₀ ch s m = (adminNext rq s.1, s.2) := by
  unfold kvEntryOn
  rw [if_pos ⟨ht, hd⟩, hdec]
  simp only [if_pos (And.intro hv ha)]

/-- **A KV entry the auth layer lets through is today's** (the auth state kept). -/
theorem kvEntryOn_of_granted (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq)
    (hna : apply.needAdminPermission rq = false) (hg : kvGranted s.1 rq) :
    kvEntryOn c₀ ch s m = (s.1, kvEntry c₀ ch s.2 m) := by
  unfold kvEntryOn
  split
  · rw [hdec]
    simp only [hna, Bool.false_eq_true, and_false, ↓reduceIte, not_true_eq_false, hg]
  · rfl

/-- **A KV entry the auth layer refuses keeps the auth state and the log.** -/
theorem kvEntryOn_of_refused (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hr : ¬ kvGranted s.1 rq) :
    kvEntryOn c₀ ch s m = s := by
  unfold kvEntryOn
  rw [if_pos ⟨ht, hd⟩, hdec]
  simp only [hna, Bool.false_eq_true, and_false, ↓reduceIte, hk, true_and, hr, not_false_eq_true]

/-- **With auth disabled throughout, the mode-`on` model is today's**: if the start's auth state is
disabled and no entry is an admin entry, every KV entry is let through and the auth state is kept,
so the log is `kvRaftOf`'s. -/
theorem kvRaftOfOn_disabled (c₀ : w64) (ch : apply.Chain) (st₀ : auth.AuthState) (log₀ : mvcc.Log)
    (A : List EntryModel) (hen : st₀.enabled = false)
    (hA : ∀ m ∈ A, ∀ rq, apply.irrDecode m.data = some rq → apply.needAdminPermission rq = false) :
    kvRaftOfOn c₀ ch (st₀, log₀) A = (st₀, kvRaftOf c₀ ch log₀ A) := by
  induction A generalizing log₀ with
  | nil => rfl
  | cons m A ih =>
    have hm := hA m (List.mem_cons_self ..)
    have hstep : kvEntryOn c₀ ch (st₀, log₀) m = (st₀, kvEntry c₀ ch log₀ m) := by
      by_cases hc : m.typ = W32 0 ∧ m.data ≠ []
      · cases hdec : apply.irrDecode m.data with
        | some rq =>
          unfold kvEntryOn
          rw [if_pos hc, hdec]
          have hna := hm rq hdec
          have hg : kvGranted st₀ rq := Or.inl hen
          simp only [hna, Bool.false_eq_true, and_false, ↓reduceIte, hg, not_true_eq_false]
        | none =>
          unfold kvEntryOn kvEntry
          rw [if_pos hc, hdec, if_pos hc.1, if_neg hc.2]
      · unfold kvEntryOn
        rw [if_neg hc]
    show List.foldl (kvEntryOn c₀ ch) (kvEntryOn c₀ ch (st₀, log₀) m) A =
      (st₀, List.foldl (kvEntry c₀ ch) (kvEntry c₀ ch log₀ m) A)
    rw [hstep]
    exact ih (kvEntry c₀ ch log₀ m) (fun m' hm' => hA m' (List.mem_cons_of_mem _ hm'))

end pure

/-! ## The mode-`on` log premises -/

section pure2
variable [ext : FfiSyntax]

/-- **An entry of the mode-`on` log**: a normal entry with data decodes to a plain request of the
proposers' kinds (today's `plainReq`, D44) or an admitted admin request (`apply.adminKindOk`). -/
def plainEntryOn (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    plainReq rq ∨ apply.adminKindOk rq

/-- Every entry of the mode-`on` log. -/
def plainLogOn (A : List EntryModel) : Prop := ∀ m ∈ A, plainEntryOn m

theorem plainEntryOn_of_plain (m : EntryModel) (h : plainEntry m) :
    plainEntryOn m := fun ht hd rq hdec => Or.inl (h ht hd rq hdec)

/-- **The entry is determinate at the state `s` it is applied at** (see the header): an admin entry
above `c₀` has one successor (`authDet`), a KV entry's check is decided (`kvDet`). -/
def entryDetOn (c₀ : w64) (s : auth.AuthState × mvcc.Log) (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    (uint.Z c₀ < uint.Z m.index → apply.needAdminPermission rq = true → authDet rq s.1) ∧
    (apply.isKVKind (apply.dispatchKind rq) = true → kvDet s.1 rq)

/-- **Every entry of `A` is determinate at the state the model reaches before it.** -/
def detLogOn (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log) (A : List EntryModel) :
    Prop :=
  ∀ (i : Nat) (m : EntryModel), A[i]? = some m → entryDetOn c₀ (kvRaftOfOn c₀ ch s₀ (A.take i)) m

theorem detLogOn_nil (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log) :
    detLogOn c₀ ch s₀ [] := by
  intro i m h; simp at h

/-- `detLogOn` of a snoc: the prefix's, and the new entry's at the prefix's model. -/
theorem detLogOn_snoc (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
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
theorem detLogOn_prefix (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (B L : List EntryModel) (hp : B <+: L) (h : detLogOn c₀ ch s₀ L) : detLogOn c₀ ch s₀ B := by
  obtain ⟨C, rfl⟩ := hp
  intro i m hm
  have hi : i < B.length := (List.getElem?_eq_some_iff.mp hm).1
  have h' := h i m (by rw [List.getElem?_append_left hi]; exact hm)
  rwa [List.take_append_of_le_length (Nat.le_of_lt hi)] at h'

/-- **The last entry of a determinate log is determinate at the state before it** (what the apply
thread needs of the entry it applies). -/
theorem detLogOn_last (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (A : List EntryModel) (m : EntryModel) (h : detLogOn c₀ ch s₀ (A ++ [m])) :
    entryDetOn c₀ (kvRaftOfOn c₀ ch s₀ A) m := by
  have h' := h A.length m (by simp)
  rwa [List.take_left' rfl] at h'

/-- **An entry of a good shape in the mode `on`** (`entryShape`, whose request clause `rqShape`
excludes every admin kind, or an admitted admin request with an id). -/
def entryShapeOn (m : EntryModel) : Prop :=
  (m.typ = W32 0 → m.data = [] ∨ ∃ rq, apply.irrDecode m.data = some rq ∧
      (∃ id, apply.irrId rq = some id) ∧ (rqShape rq ∨ apply.adminKindOk rq)) ∧
    (m.typ ≠ W32 0 → ccIdOf m.data = W64 0)

/-- Every entry of a log has a good shape in the mode `on`. -/
def logShapeOn (L : List EntryModel) : Prop := ∀ m ∈ L, entryShapeOn m

theorem entryShapeOn_of_entryShape (m : EntryModel) (h : entryShape m) :
    entryShapeOn m := by
  refine ⟨fun ht => ?_, h.2⟩
  rcases h.1 ht with h | ⟨rq, hd, hid, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨rq, hd, hid, Or.inl hs⟩

end pure2

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The KV model of the committed log `L` in the mode `on`**, from the start's auth state `st₀`
(the store's state at the server's start) and the start's log. -/
def kvModelOn (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) : mvcc.Log :=
  (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).2

theorem kvModelOn_nil (γk : KVNames) (st₀ : auth.AuthState) : kvModelOn γk st₀ [] = γk.log0 := rfl

/-- **The workload facts of the committed log in the mode `on`** (`kvWork` with `logShapeOn`). -/
def kvWorkOn (cfg : RaftNames) (γk : KVNames) (L : List EntryModel) : IProp GF :=
  iprop(⌜logShapeOn L ∧ ccLogOk cfg L⌝ ∗ [∗list] m ∈ L, entryClaim γk.ids m)

instance kvWorkOn_persistent (cfg : RaftNames) (γk : KVNames) (L : List EntryModel) :
    Persistent (kvWorkOn (GF := GF) cfg γk L) := by
  unfold kvWorkOn; infer_instance

instance kvWorkOn_timeless (cfg : RaftNames) (γk : KVNames) (L : List EntryModel) :
    Timeless (kvWorkOn (GF := GF) cfg γk L) := by
  unfold kvWorkOn; infer_instance

/-- `kvWork` gives `kvWorkOn`. -/
theorem kvWorkOn_of_kvWork (cfg : RaftNames) (γk : KVNames) (L : List EntryModel) :
    kvWork (GF := GF) cfg γk L ⊢ kvWorkOn cfg γk L := by
  unfold kvWork kvWorkOn
  iintro ⟨%h, #H⟩
  iframe H
  ipureintro
  exact ⟨fun m hm => entryShapeOn_of_entryShape m (h.1 m hm), h.2⟩

/-- **The KV invariant in the mode `on`** (`kvInv`'s, with the mode-`on` model, see the header):
the server's half of the committed log `L` (after `ai0`, consecutive, every entry of the mode-`on`
log and determinate at the state it is applied at, every entry above the start's consistent index)
and the other half of the state's ghost variable at the state of `L`'s mode-`on` model; the start's
chain the base chain with auth **enabled** and no alarm, the start log not empty; the workload
facts (`kvWorkOn`). -/
def kvInvOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) : IProp GF :=
  inv kvN iprop(∃ L : List EntryModel,
    srvRLog γ L ∗ ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L)) ∗
    ⌜plainLogOn L ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) L ∧ srvIdxOkW γ.ai0 L ∧
      uint.Z γk.c0 ≤ uint.Z γ.ai0 + L.length ∧
      γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ []⌝ ∗ kvWorkOn γ.raft γk L)

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

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The mode-`on` KV invariant's start chain has the auth layer on** (`kvInv_ch0_off`'s
counterpart): unlike `kvInv`, it agrees with `NewServer.specM true`'s premise on the start chain. -/
theorem kvInvOn_ch0 (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ ={⊤}=∗ ⌜γk.ch0 = apply.alarmChain true false false⌝ := by
  iintro #Hinv
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  exact Hok.2.2.2.2.1

/-- **The mode-`on` KV invariant can be allocated** at the empty committed log (as `kvInv`'s, at
the server's start): the server's half of the empty log, the state's half at the start log, the
start chain with auth on, the start log not empty and the consistent index within the start's. So
`kvInvOn` is satisfiable, unlike `kvInv` at a mode-`on` chain (`kvInv_ch0_on_false`). -/
theorem kvInvOn_alloc (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (E : CoPset)
    (hch : γk.ch0 = apply.alarmChain true false false) (hlog : γk.log0 ≠ [])
    (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0) :
    ⊢ srvRLog (GF := GF) γ [] -∗ ghostVar γk.st (1 : Qp).half (kvStateOf γk.log0) ={E}=∗
      kvInvOn γ γk st₀ := by
  iintro HL Hσ
  iunfold kvInvOn
  iapply inv_alloc
  inext
  iexists []
  rw [kvModelOn_nil]
  isplitl [HL]
  · iexact HL
  isplitl [Hσ]
  · iexact Hσ
  isplitr
  · ipureintro
    refine ⟨fun m hm => by simp at hm, detLogOn_nil _ _ _, ?_, by simpa using hc, hch, hlog⟩
    intro n m hm; simp at hm
  · iunfold kvWorkOn
    isplitr
    · ipureintro
      exact ⟨fun m hm => by simp at hm, fun m hm => by simp at hm⟩
    · iapply BigSepL.bigSepL_nil.2
      iempintro

/-- **The committed log is a mode-`on` log, determinate, and the start chain has auth on** (the
mode-`on` invariant's; `kv_log_plain`'s counterpart): what the apply thread reads of a committed
prefix `B` before applying its last entry. -/
theorem kv_log_plain_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (B : List EntryModel) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ srvRaftLogInv γ -∗ srvRLogLb γ B ={⊤}=∗
      ⌜plainLogOn B ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) B ∧
        γk.ch0 = apply.alarmChain true false false⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L B $$ Hr HL HB with ⟨HL, -, %Hp⟩
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  exact ⟨fun m hm => Hok.1 m (Hp.subset hm), detLogOn_prefix _ _ _ B L Hp Hok.2.1, Hok.2.2.2.2.1⟩

end lemmas

end EtcdGrove
end Perennial
