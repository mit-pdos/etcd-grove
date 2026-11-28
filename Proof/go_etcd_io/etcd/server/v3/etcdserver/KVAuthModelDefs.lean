/-
**The auth-aware KV model, pure part** (moved out of `KVAuthModel.lean`, 2026-11-27, so that
`InvRequest.lean` can define the KV model over it): the admin step (`adminStateR`, `adminNext`),
the KV check (`reqPerms`, `kvGranted`, `kvGrantedL`), one entry's effect on the auth state, the KV
log and the lease table (`kvEntryOn`), its fold (`kvRaftOfOn`) and the auth history along a log
(`admStatesR`). `KVAuthModel.lean`'s header explains the model.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchKVL
public import Proof.go_etcd_io.etcd.server.v3.auth.Steps
public import Spec.google_golang_org.protobuf.proto.MarshalIRR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-! ## The admin entries' step -/

/-- The state after an admin operation's outcome at `st`: a refusal and nothing to do leave it,
`next` replaces it. -/
def outState (st : auth.AuthState) : auth.Outcome → auth.AuthState
  | .err _ => st
  | .same => st
  | .next st' => st'

/-- A step relation's successors of `st`, as states. -/
def authRelState (R : auth.StepRel) (st st' : auth.AuthState) : Prop :=
  ∃ o, R st o ∧ st' = outState st o

open Classical in
/-- **An admitted admin entry's effect on the auth state** (`st` to `st'`): with the principal
admin-permitted at `st` (`auth.adminOk`; `authApplierV3.Apply` checks it of `needAdminPermission`
requests), its kind's step (`auth/Steps.lean`; the flag the steps read is `st`'s: the apply thread
applies at the latest state); otherwise nothing. `UserAdd` may also be refused with
`ErrNoPasswordUser` (the state kept), unless its password choice cannot fail (`UserAddModel.pwSure`:
the request model keeps it); `UserChangePassword`'s step decides that refusal itself
(`auth.userChangePasswordF` with `auth.selectPwOk` of the request's passwords and the user's
`NoPassword`; nomode D3 follow-up (a), 2026-11-28). An entry of another kind keeps the state.
(Nomode D3, 2026-11-28: the six kinds from `AuthDisable` on.) -/
def adminStateR (rq : apply.IRRModel) (st st' : auth.AuthState) : Prop :=
  if auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))) then
    match apply.dispatchKind rq with
    | .authUserAdd =>
        match rq.authUserAdd with
        | some m => (¬ m.pwSure ∧ st' = st) ∨
            authRelState (auth.stepOf (auth.userAddF m.name m.noPassword)) st st'
        | none => st' = st
    | .authRoleAdd =>
        match rq.authRoleAdd with
        | some n => authRelState (auth.stepOf (auth.roleAddF n)) st st'
        | none => st' = st
    | .authUserGrantRole =>
        match rq.authUserGrantRole with
        | some (u, r) => authRelState (auth.userGrantRoleR u r) st st'
        | none => st' = st
    | .authRoleGrantPermission =>
        match rq.authRoleGrantPermission with
        | some (r, w) => authRelState (auth.roleGrantPermissionR r w) st st'
        | none => st' = st
    | .authEnable => authRelState (auth.stepOf (auth.authEnableF st.enabled)) st st'
    | .authDisable => authRelState (auth.stepOf (auth.authDisableF st.enabled)) st st'
    | .authUserDelete =>
        match rq.authUserDelete with
        | some n => authRelState (auth.stepOf (auth.userDeleteF st.enabled n)) st st'
        | none => st' = st
    | .authUserChangePassword =>
        match rq.authUserChangePassword with
        | some m =>
            authRelState (auth.stepOf (auth.userChangePasswordF m.name (auth.selectPwOk m.password m.hashed))) st st'
        | none => st' = st
    | .authUserRevokeRole =>
        match rq.authUserRevokeRole with
        | some (n, ro) => authRelState (auth.stepOf (auth.userRevokeRoleF st.enabled n ro)) st st'
        | none => st' = st
    | .authRoleDelete =>
        match rq.authRoleDelete with
        | some ro => authRelState (auth.stepOf (auth.roleDeleteF st.enabled ro)) st st'
        | none => st' = st
    | .authRoleRevokePermission =>
        match rq.authRoleRevokePermission with
        | some (ro, k, e) => authRelState (auth.roleRevokePermissionR ro k e) st st'
        | none => st' = st
    | _ => st' = st
  else st' = st

/-- **An admin request's step at `st` to the outcome `o`** (`adminStateR`'s kinds, its admin check
aside): the request model's step of its kind (`AuthEnable`'s at `st`'s own flag); no other kind
steps. -/
def adminStepO (rq : apply.IRRModel) (st : auth.AuthState) (o : auth.Outcome) : Prop :=
  match apply.dispatchKind rq with
  | .authUserAdd => ∃ m, rq.authUserAdd = some m ∧ auth.stepOf (auth.userAddF m.name m.noPassword) st o
  | .authRoleAdd => ∃ n, rq.authRoleAdd = some n ∧ auth.stepOf (auth.roleAddF n) st o
  | .authUserGrantRole =>
      ∃ u r, rq.authUserGrantRole = some (u, r) ∧ auth.userGrantRoleR u r st o
  | .authRoleGrantPermission =>
      ∃ n w, rq.authRoleGrantPermission = some (n, w) ∧ auth.roleGrantPermissionR n w st o
  | .authEnable => auth.stepOf (auth.authEnableF st.enabled) st o
  | .authDisable => auth.stepOf (auth.authDisableF st.enabled) st o
  | .authUserDelete => ∃ n, rq.authUserDelete = some n ∧ auth.stepOf (auth.userDeleteF st.enabled n) st o
  | .authUserChangePassword =>
      ∃ m, rq.authUserChangePassword = some m ∧
        auth.stepOf (auth.userChangePasswordF m.name (auth.selectPwOk m.password m.hashed)) st o
  | .authUserRevokeRole =>
      ∃ n ro, rq.authUserRevokeRole = some (n, ro) ∧
        auth.stepOf (auth.userRevokeRoleF st.enabled n ro) st o
  | .authRoleDelete => ∃ ro, rq.authRoleDelete = some ro ∧ auth.stepOf (auth.roleDeleteF st.enabled ro) st o
  | .authRoleRevokePermission =>
      ∃ ro k e, rq.authRoleRevokePermission = some (ro, k, e) ∧ auth.roleRevokePermissionR ro k e st o
  | _ => False

/-- **An admin entry succeeded from `st` to `st'`** (the auth plan's E3x, 2026-10-27): its
principal admin-permitted at `st` and its step's outcome no error, `st'` the state after it
(`adminStateR`'s successful successors: neither the refusal nor the step's error). -/
def adminStepOk (rq : apply.IRRModel) (st st' : auth.AuthState) : Prop :=
  auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))) ∧
    ∃ o, adminStepO rq st o ∧ (∀ e, o ≠ .err e) ∧ st' = outState st o

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

/-- **An admin step's outcome, with the principal admin-permitted, is one of the model's**
(`adminStepO`, `adminStateR`). -/
theorem adminStateR_of_stepO (rq : apply.IRRModel) (st : auth.AuthState) (o : auth.Outcome)
    (ha : auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))))
    (hO : adminStepO rq st o) : adminStateR rq st (outState st o) := by
  unfold adminStateR
  rw [if_pos ha]
  unfold adminStepO at hO
  split at hO <;> rename_i hk
  · obtain ⟨m, hm, h⟩ := hO; simp only [hm]; exact Or.inr ⟨o, h, rfl⟩
  · obtain ⟨n, hn, h⟩ := hO; simp only [hn]; exact ⟨o, h, rfl⟩
  · obtain ⟨u, r, hu, h⟩ := hO; simp only [hu]; exact ⟨o, h, rfl⟩
  · obtain ⟨n, w, hn, h⟩ := hO; simp only [hn]; exact ⟨o, h, rfl⟩
  · exact ⟨o, hO, rfl⟩
  · exact ⟨o, hO, rfl⟩
  · obtain ⟨n, hn, h⟩ := hO; simp only [hn]; exact ⟨o, h, rfl⟩
  · obtain ⟨m, hm, h⟩ := hO; simp only [hm]; exact ⟨o, h, rfl⟩
  · obtain ⟨n, ro, hn, h⟩ := hO; simp only [hn]; exact ⟨o, h, rfl⟩
  · obtain ⟨n, hn, h⟩ := hO; simp only [hn]; exact ⟨o, h, rfl⟩
  · obtain ⟨ro, k, e, hn, h⟩ := hO; simp only [hn]; exact ⟨o, h, rfl⟩
  · exact hO.elim

/-- **A successful admin step is one of the model's** (`adminStepOk`, `adminStateR`). -/
theorem adminStateR_of_stepOk (rq : apply.IRRModel) (st st' : auth.AuthState)
    (h : adminStepOk rq st st') : adminStateR rq st st' := by
  obtain ⟨ha, o, hO, -, rfl⟩ := h
  exact adminStateR_of_stepO rq st o ha hO

/-- **A successful admin step at a determinate entry is the model's step**. -/
theorem adminNext_of_stepOk (rq : apply.IRRModel) (st st' : auth.AuthState) (hd : authDet rq st)
    (h : adminStepOk rq st st') : adminNext rq st = st' :=
  adminNext_of_det rq st st' hd (adminStateR_of_stepOk rq st st' h)

/-! ## The KV entries' check -/

mutual
/-- The permissions a transaction's operation needs (`checkTxnReqsPermission`'s walk, `opClass`), of
its wire operation (E3e: a put's `PrevKv` kept): a get's read, a put's write of its key and with
`PrevKv` its read (`checkPutAuth`, `apply.putPerms`), a delete's write and `PrevKv` read, a nested
transaction's comparisons and both branches. -/
def opPerms : txn.TxnOpW → List apply.Perm3
  | .get o => [(o.key, o.base.rangeEnd, .read)]
  | .put o => apply.putPerms o
  | .delete o => (o.key, o.base.rangeEnd, .write) ::
      if o.base.prevKV then [(o.key, o.base.rangeEnd, .read)] else []
  | .txn cs ts es => cs.map (fun cm => (cm.key, cm.rangeEnd, .read)) ++ opsPerms ts ++ opsPerms es

/-- The permissions a list of operations needs, in order. -/
def opsPerms : List txn.TxnOpW → List apply.Perm3
  | [] => []
  | op :: ops => opPerms op ++ opsPerms ops
end

/-- **The permissions a KV request needs** (`apply.reqClass`, purely): a put's (`apply.putPerms`),
a delete's write and `PrevKv` read of its range, a range's read, a transaction's comparisons'
reads and both branches' operations (of its wire transaction, `txnW`: a put's `PrevKv` read
included, E3e). -/
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
  | .txn => match rq.txnW with
      | some t => t.cmps.map (fun cm => (cm.key, cm.rangeEnd, .read)) ++ opsPerms t.thenOps ++
          opsPerms t.elseOps
      | none => []
  | _ => []

/-- **The auth layer lets the KV request `rq` through at `st`** (`isOpPermitted` for each of its
permissions, at one state: the apply thread is the store's only writer): every permission the
request needs passes, each check passing when auth is disabled, or when the principal's revision
is not `0` (`ErrUserEmpty`) and not below the store's (`ErrAuthOldRevision`) and its user exists
with the root role or with permissions covering it. A request needing no permission (a transaction
without comparisons or operations) is let through whatever the principal, as the code applies it
unchecked (E2v; until then the model asked the revision and the user of it too). -/
def kvGranted (st : auth.AuthState) (rq : apply.IRRModel) : Prop :=
  ∀ x ∈ reqPerms rq, st.enabled = false ∨
    ((auth.authInfoM (apply.principalOf rq)).rev ≠ 0 ∧
      st.revision ≤ (auth.authInfoM (apply.principalOf rq)).rev ∧
      ∃ u, st.users !! (auth.authInfoM (apply.principalOf rq)).user = some u ∧
        (auth.isRoot u ∨ auth.covers st u x.2.2 x.1 x.2.1))

/-- With auth disabled, every request is let through. -/
theorem kvGranted_of_disabled (st : auth.AuthState) (rq : apply.IRRModel)
    (hen : st.enabled = false) : kvGranted st rq :=
  fun _ _ => Or.inl hen

/-- **An enabled auth state lets no request with a permission through for a user it does not
have** (the empty user, which `UserAdd` refuses, among them; the auth-mode merge's step 5). -/
theorem kvGranted_emptyUser (st : auth.AuthState) (rq : apply.IRRModel)
    (hen : st.enabled = true) (hne : reqPerms rq ≠ [])
    (hu : st.users !! (auth.authInfoM (apply.principalOf rq)).user = none) : ¬ kvGranted st rq := by
  intro h
  cases hp : reqPerms rq with
  | nil => exact hne hp
  | cons x xs =>
    rcases h x (by rw [hp]; exact List.mem_cons_self) with h1 | ⟨-, -, u, hu', -⟩
    · rw [hen] at h1; cases h1
    · rw [hu] at hu'; cases hu'

/-- A request needing no permission is let through. -/
theorem kvGranted_of_nil (st : auth.AuthState) (rq : apply.IRRModel) (h : reqPerms rq = []) :
    kvGranted st rq := by
  intro x hx; rw [h] at hx; cases hx

/-- **No range end of the request is `"\x00"`** (a premise of the workload; since E3o kept by the
mode-`on` log, `plainEntryOn`): the one end at which a check can see another range than the
model's (`authEndOf`: a non-`nil` empty `RangeEnd` on the wire, which the model reads as `"\x00"`). -/
def noZeroEnds (rq : apply.IRRModel) : Prop := ∀ x ∈ reqPerms rq, x.2.1 ≠ [W8 0]

/-- **Every permission the request needs is of the shape the permission cache decides** (since E3o
kept by the mode-`on` log, `plainEntryOn`): the check is decided at any state (`kvDet`). -/
def kvShapeAll (rq : apply.IRRModel) : Prop :=
  ∀ x ∈ reqPerms rq, auth.reqShape x.1 x.2.1

theorem putPerms_noZero (o : OpFull) : ∀ x ∈ apply.putPerms o, x.2.1 ≠ [W8 0] := by
  intro x hx
  unfold apply.putPerms at hx
  split at hx <;> simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx <;>
    rcases hx with rfl | rfl <;> simp

mutual
theorem opPerms_noZero : ∀ op : txn.TxnOpW, txnOpNoZeroEnd op.toOp →
    ∀ x ∈ opPerms op, x.2.1 ≠ [W8 0]
  | .get o, h, x, hx => by
    simp only [opPerms, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    subst hx; exact h
  | .put o, _, x, hx => putPerms_noZero o x hx
  | .delete o, h, x, hx => by
    simp only [opPerms] at hx
    split at hx <;> simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx <;>
      rcases hx with rfl | rfl <;> exact h
  | .txn cs ts es, h, x, hx => by
    obtain ⟨hc, ht, he⟩ := h
    simp only [opPerms, List.mem_append, List.mem_map] at hx
    rcases hx with (⟨cm, hcm, rfl⟩ | hx) | hx
    · exact hc cm hcm
    · exact opsPerms_noZero ts ht x hx
    · exact opsPerms_noZero es he x hx

theorem opsPerms_noZero : ∀ ops : List txn.TxnOpW, txnOpsNoZeroEnd (txn.TxnOpW.toOps ops) →
    ∀ x ∈ opsPerms ops, x.2.1 ≠ [W8 0]
  | [], _, x, hx => by simp [opsPerms] at hx
  | op :: ops, h, x, hx => by
    obtain ⟨h1, h2⟩ := h
    simp only [opsPerms, List.mem_append] at hx
    rcases hx with hx | hx
    · exact opPerms_noZero op h1 x hx
    · exact opsPerms_noZero ops h2 x hx
end

/-- **The wire's `irrNoZeroEnd` (the proposers') gives `noZeroEnds`** (E3o). -/
theorem noZeroEnds_of_irr (rq : apply.IRRModel) (h : irrNoZeroEnd rq) : noZeroEnds rq := by
  obtain ⟨hr, hd, ht⟩ := h
  intro x hx
  unfold reqPerms at hx
  split at hx
  · split at hx
    · exact putPerms_noZero _ x hx
    · cases hx
  · split at hx
    · rename_i o ho
      split at hx <;> simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx <;>
        rcases hx with rfl | rfl <;> exact hd o ho
    · cases hx
  · split at hx
    · rename_i o ho
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
      subst hx; exact hr o ho
    · cases hx
  · split at hx
    · rename_i t ht'
      have h' := ht t.toModel (by simp [apply.IRRModel.txn, ht'])
      obtain ⟨hc, hth, hel⟩ := h'
      simp only [List.mem_append, List.mem_map] at hx
      rcases hx with ((⟨cm, hcm, rfl⟩ | hx) | hx)
      · exact hc cm hcm
      · exact opsPerms_noZero _ hth x hx
      · exact opsPerms_noZero _ hel x hx
    · cases hx
  · cases hx

/-- **The check is decided at `st`**: with auth enabled, every permission the request needs is of
the shape the permission cache decides (`auth.reqShape`). -/
def kvDet (st : auth.AuthState) (rq : apply.IRRModel) : Prop :=
  st.enabled = true → ∀ x ∈ reqPerms rq, auth.reqShape x.1 x.2.1

/-! ## The model -/

/-- **The mode-`on` model's state** (auth-lease S3a): the auth state, the KV log and the lease table. -/
abbrev OnState := auth.AuthState × mvcc.Log × LeaseTable

/-- **One lease's keys writable by the principal at `st`** (auth-lease S3a; `checkLeasePuts`' check of one
lease at one state): auth disabled, or the principal an admin there (no revision: `IsAdminPermitted`), or
every key attached to the lease writable by the principal (a lease attaching no key passes). -/
def leaseOk (st : auth.AuthState) (a : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64) : Prop :=
  st.enabled = false ∨ auth.adminOk st (some (auth.authInfoM a)) ∨
    ∀ k : GoString, I.lookup ⟨k⟩ = some id →
      ((auth.authInfoM a).rev ≠ 0 ∧ st.revision ≤ (auth.authInfoM a).rev ∧
        ∃ u, st.users !! (auth.authInfoM a).user = some u ∧
          (auth.isRoot u ∨ auth.covers st u .write k []))

/-- **The lease part of the apply-time check** (auth-lease S3a; `checkLeasePuts` of a put, of a
transaction's puts, of a revocation); a grant is not checked at apply. -/
def leaseGrantedM (st : auth.AuthState) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (rq : apply.IRRModel) : Prop :=
  match apply.dispatchKind rq with
  | .put => ∀ o, rq.put = some o → leaseOk st (apply.principalOf rq) I o.leaseID
  | .txn => ∀ t, rq.txnW = some t → ∀ o ∈ apply.txnPutsW t,
      leaseOk st (apply.principalOf rq) I o.leaseID
  | .leaseRevoke => ∀ id, rq.leaseRevoke = some id → leaseOk st (apply.principalOf rq) I id
  | _ => True

/-- **The auth layer lets `rq` through at `st`, its lease part at the lease items `I`** (auth-lease S3a). -/
def kvGrantedL (st : auth.AuthState) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (rq : apply.IRRModel) : Prop :=
  kvGranted st rq ∧ leaseGrantedM st I rq

/-- With auth disabled, every lease check passes. -/
theorem leaseOk_of_disabled (st : auth.AuthState) (a : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64) (hen : st.enabled = false) :
    leaseOk st a I id := Or.inl hen

/-- A lease no key is attached to passes. -/
theorem leaseOk_of_none (st : auth.AuthState) (a : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (h : ∀ k : GoString, I.lookup ⟨k⟩ ≠ some id) : leaseOk st a I id :=
  Or.inr (Or.inr fun k hk => absurd hk (h k))

theorem leaseGrantedM_of_disabled (st : auth.AuthState)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (rq : apply.IRRModel)
    (hen : st.enabled = false) : leaseGrantedM st I rq := by
  unfold leaseGrantedM
  split
  · intro _ _; exact Or.inl hen
  · intro _ _ _ _; exact Or.inl hen
  · intro _ _; exact Or.inl hen
  · trivial

theorem kvGrantedL_of_disabled (st : auth.AuthState)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (rq : apply.IRRModel)
    (hen : st.enabled = false) : kvGrantedL st I rq :=
  ⟨kvGranted_of_disabled st rq hen, leaseGrantedM_of_disabled st I rq hen⟩

/-- The lease `0` attaches no key in any state (`leaseItemsOf_ne_zero`). -/
theorem leaseItemsOf_zero_none (log : mvcc.Log) :
    ∀ k : GoString, (mvcc.leaseItemsOf (mvcc.stateAfter log)).lookup ⟨k⟩ ≠ some (W64 0) :=
  fun k => mvcc.leaseItemsOf_ne_zero _ _

mutual
/-- A plain wire operation's puts have the lease `0` (`txn.opPlain` of its model). -/
theorem opPutsW_plain : ∀ (op : txn.TxnOpW), txn.opPlain op.toOp → ∀ o ∈ apply.opPutsW op,
    o.leaseID = W64 0
  | .get _, _, o, ho => by simp [apply.opPutsW] at ho
  | .delete _, _, o, ho => by simp [apply.opPutsW] at ho
  | .put o', h, o, ho => by
    simp only [apply.opPutsW, List.mem_singleton] at ho
    subst ho
    simp only [txn.TxnOpW.toOp, txn.putTxnOp] at h
    by_cases h1 : o.ignoreValue = true <;> by_cases h2 : o.ignoreLease = true <;>
      simp [h1, h2, txn.opPlain] at h
    · simpa using h
    · exact h
  | .txn _ ts es, h, o, ho => by
    simp only [txn.TxnOpW.toOp, txn.opPlain] at h
    simp only [apply.opPutsW, List.mem_append] at ho
    rcases ho with ho | ho
    · exact opsPutsW_plain ts h.1 o ho
    · exact opsPutsW_plain es h.2 o ho

theorem opsPutsW_plain : ∀ (ops : List txn.TxnOpW), txn.opsPlain (txn.TxnOpW.toOps ops) →
    ∀ o ∈ apply.opsPutsW ops, o.leaseID = W64 0
  | [], _, o, ho => by simp [apply.opsPutsW] at ho
  | op :: ops, h, o, ho => by
    simp only [txn.TxnOpW.toOps, txn.opsPlain] at h
    simp only [apply.opsPutsW, List.mem_append] at ho
    rcases ho with ho | ho
    · exact opPutsW_plain op h.1 o ho
    · exact opsPutsW_plain ops h.2 o ho
end

/-- **A plain transaction's puts have the lease `0`** (auth-lease S2). -/
theorem txnPutsW_plain (t : txn.TxnModelW) (h : txn.txnPlain t.toModel) :
    ∀ o ∈ apply.txnPutsW t, o.leaseID = W64 0 := by
  intro o ho
  simp only [apply.txnPutsW, List.mem_append] at ho
  simp only [txn.txnPlain, txn.TxnModelW.toModel] at h
  rcases ho with ho | ho
  · exact opsPutsW_plain _ h.1 o ho
  · exact opsPutsW_plain _ h.2 o ho

/-- A plain request's lease part passes at any state, at the lease items of a log's state (no key is
attached to the lease `0`). -/
theorem leaseGrantedM_of_plainCover (st : auth.AuthState) (log : mvcc.Log) (rq : apply.IRRModel)
    (hp : plainCover rq) : leaseGrantedM st (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq := by
  have hz0 := leaseItemsOf_zero_none log
  have h0 : leaseOk st (apply.principalOf rq) (mvcc.leaseItemsOf (mvcc.stateAfter log)) (W64 0) :=
    leaseOk_of_none _ _ _ _ hz0
  unfold leaseGrantedM
  split
  · rename_i hk
    intro o ho
    unfold plainCover at hp; rw [hk] at hp
    rw [hp.2.2 o ho]; exact h0
  · rename_i hk
    intro t htx o ho
    have hpl : txn.txnPlain t.toModel := by
      unfold plainCover at hp; rw [hk] at hp
      exact hp.2.2 t.toModel (by rw [← apply.IRRModel.txnW_map, htx]; rfl)
    rw [txnPutsW_plain t hpl o ho]; exact h0
  · rename_i hk
    unfold plainCover at hp; rw [hk] at hp; exact hp.elim
  · trivial

/-- **The kinds `dispatch` applies as an admin step** (`authApplierV3`'s admin requests, the field
`dispatch` reads first being one `needAdminPermission` reads). -/
def adminDispatchKind : apply.ReqKind → Bool
  | .authEnable | .authDisable | .authUserAdd | .authUserDelete | .authUserChangePassword
  | .authUserGrantRole | .authUserRevokeRole | .authRoleAdd | .authRoleGrantPermission
  | .authRoleRevokePermission | .authRoleDelete | .authUserList | .authRoleList => true
  | _ => false

/-- A request `dispatch` applies as an admin step needs the admin permission. -/
theorem needAdminPermission_of_adminDispatchKind (rq : apply.IRRModel)
    (h : adminDispatchKind (apply.dispatchKind rq) = true) : apply.needAdminPermission rq = true := by
  cases hk : apply.dispatchKind rq <;> rw [hk] at h <;>
    simp only [adminDispatchKind, Bool.false_eq_true] at h <;>
    simp only [apply.dispatchKind, apply.ite_eq_iff', reduceCtorEq, and_false, false_or, or_false,
      and_true] at hk <;>
    simp [apply.needAdminPermission, hk]

/-- **A refused admin request keeps the state**: at a state that does not admit its principal,
the model's step is the identity (`adminStateR`'s refusal). -/
theorem adminNext_refused (rq : apply.IRRModel) (st : auth.AuthState)
    (h : ¬ auth.adminOk st (some (auth.authInfoM (apply.principalOf rq)))) :
    adminNext rq st = st := by
  have hr : ∀ st', adminStateR rq st st' ↔ st' = st := by
    intro st'; unfold adminStateR; simp [h]
  exact adminNext_of_det rq st st ⟨st, (hr st).2 rfl, fun st'' h'' => (hr st'').1 h''⟩ ((hr st).2 rfl)

open Classical in
/-- **An entry's effect in the mode `on`** (auth-lease S3a: on the triple state; D1, 2026-11-27:
`authApplierV3.Apply`'s order), from the consistent index `c₀` with the chain `ch`, on the auth
state, the KV log and the lease table `s`: a normal entry with data that decodes to `rq` is, if `rq`
needs the admin permission (`needAdminPermission`) and its principal is not admin-permitted at
`s.1` (`IsAdminPermitted`), nothing; else, above `c₀` (`v3`) and of a kind `dispatch` applies as
an admin step (`adminDispatchKind`), the admin step (the log and the table kept); else, of a kind
the auth layer checks (`apply.authKVKind`: the KV kinds and the revocation) that it refuses at
`s.1`, its lease part at the log's lease items, nothing; otherwise today's `kvEntry`/`kvTable` at
the table (a request with an admin field beside a KV field dispatches the KV one). -/
def kvEntryOn (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel) : OnState :=
  if m.typ = W32 0 ∧ m.data ≠ [] then
    match apply.irrDecode m.data with
    | some rq =>
      if apply.needAdminPermission rq = true ∧
          ¬ auth.adminOk s.1 (some (auth.authInfoM (apply.principalOf rq))) then s
      else if uint.Z c₀ < uint.Z m.index ∧ adminDispatchKind (apply.dispatchKind rq) = true then
        (adminNext rq s.1, s.2)
      else if apply.authKVKind (apply.dispatchKind rq) = true ∧
          ¬ kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq then s
      else (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)
    | none => s
  else (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)

/-- **The mode-`on` model of a raft log** `A`, from the start's state `s₀`. -/
def kvRaftOfOn (c₀ : w64) (ch : apply.Chain) (s₀ : OnState) (A : List EntryModel) : OnState :=
  A.foldl (kvEntryOn c₀ ch) s₀

theorem kvRaftOfOn_nil (c₀ : w64) (ch : apply.Chain) (s₀ : OnState) :
    kvRaftOfOn c₀ ch s₀ [] = s₀ := rfl

theorem kvRaftOfOn_append (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A B : List EntryModel) :
    kvRaftOfOn c₀ ch s₀ (A ++ B) = kvRaftOfOn c₀ ch (kvRaftOfOn c₀ ch s₀ A) B := by
  unfold kvRaftOfOn; exact List.foldl_append

/-- A mode-`on` entry's step extends the model's log (moved here from `v3rpc.ClientModel`, 2026-11-17; the
server's apply thread uses it too). -/
theorem kvEntryOn_extends (c₀ : w64) (ch : apply.Chain) (st : OnState)
    (m : EntryModel) : st.2.1 <+: (kvEntryOn c₀ ch st m).2.1 := by
  unfold kvEntryOn
  split
  · split
    · split
      · exact List.prefix_refl _
      · split
        · exact List.prefix_refl _
        · split
          · exact List.prefix_refl _
          · exact kvEntry_prefix c₀ ch st.2.2 st.2.1 m
    · exact List.prefix_refl _
  · exact kvEntry_prefix c₀ ch st.2.2 st.2.1 m

-- (strict M1, 2026-11-06) moved here from `KVApplyOn`/`KVReadOn`, below `KVStoreLaws`
-- (`restoreArgs_holds` takes the model's prefix lemmas in both modes)
/-- **A mode-`on` entry grows the log by at most one revision** (`kvEntry_grow`'s counterpart). -/
theorem kvEntryOn_grow (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel) :
    (kvEntryOn c₀ ch s m).2.1 = s.2.1 ∨ ∃ cs, (kvEntryOn c₀ ch s m).2.1 = s.2.1 ++ [cs] := by
  unfold kvEntryOn
  split
  · split
    · split
      · left; rfl
      · split
        · left; rfl
        · split
          · left; rfl
          · exact kvEntry_grow c₀ ch s.2.2 s.2.1 m
    · left; rfl
  · exact kvEntry_grow c₀ ch s.2.2 s.2.1 m

/-- **The mode-`on` model's log extends the start's** (`kvRaftOf_extends`'s counterpart). -/
theorem kvRaftOfOn_extends (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) : s₀.2.1 <+: (kvRaftOfOn c₀ ch s₀ A).2.1 := by
  induction A generalizing s₀ with
  | nil => exact List.prefix_refl _
  | cons m A ih =>
    show s₀.2.1 <+: (kvRaftOfOn c₀ ch (kvEntryOn c₀ ch s₀ m) A).2.1
    refine List.IsPrefix.trans ?_ (ih _)
    rcases kvEntryOn_grow c₀ ch s₀ m with h | ⟨cs, h⟩
    · rw [h]; exact List.prefix_refl _
    · rw [h]; exact List.prefix_append _ _

/-- **The mode-`on` model is monotone in the raft log** (`kvRaftOf_prefix`'s counterpart). -/
theorem kvRaftOfOn_prefix (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A B : List EntryModel) (h : A <+: B) :
    (kvRaftOfOn c₀ ch s₀ A).2.1 <+: (kvRaftOfOn c₀ ch s₀ B).2.1 := by
  obtain ⟨D, rfl⟩ := h
  rw [kvRaftOfOn_append]
  exact kvRaftOfOn_extends _ _ _ _

theorem kvRaftOfOn_snoc (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) (m : EntryModel) :
    kvRaftOfOn c₀ ch s₀ (A ++ [m]) = kvEntryOn c₀ ch (kvRaftOfOn c₀ ch s₀ A) m := by
  rw [kvRaftOfOn_append]; rfl

/-- An admitted admin request (`apply.adminKindOk`) needing the admin permission is of an admin
kind (`Authenticate`, the one other kind it admits, needs none). -/
theorem adminDispatchKind_of_adminKindOk (rq : apply.IRRModel) (hk : apply.adminKindOk rq)
    (ha : apply.needAdminPermission rq = true) : adminDispatchKind (apply.dispatchKind rq) = true := by
  unfold apply.adminKindOk at hk
  split at hk <;> rename_i heq <;> simp_all [adminDispatchKind]

/-- A request needing no admin permission is of no admin kind. -/
theorem adminDispatchKind_of_needAdmin_false (rq : apply.IRRModel)
    (h : apply.needAdminPermission rq = false) : adminDispatchKind (apply.dispatchKind rq) = false := by
  cases hk : adminDispatchKind (apply.dispatchKind rq)
  · rfl
  · rw [needAdminPermission_of_adminDispatchKind rq hk] at h; cases h

/-- **An admin entry above `c₀` steps the auth state and keeps the log and the table** (its
refusal, `adminNext_refused`, included). -/
theorem kvEntryOn_admin (c₀ : w64) (ch : apply.Chain) (s : OnState)
    (m : EntryModel) (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hk : adminDispatchKind (apply.dispatchKind rq) = true) :
    kvEntryOn c₀ ch s m = (adminNext rq s.1, s.2) := by
  unfold kvEntryOn
  rw [if_pos ⟨ht, hd⟩, hdec]
  by_cases hok : auth.adminOk s.1 (some (auth.authInfoM (apply.principalOf rq)))
  · simp only [hok, not_true_eq_false, and_false, ↓reduceIte, hv, hk, and_self]
  · simp only [needAdminPermission_of_adminDispatchKind rq hk, hok, not_false_eq_true, and_self,
      ↓reduceIte, adminNext_refused rq s.1 hok]

/-- **A request whose principal is not admin-permitted, needing the admin permission, keeps the
state** (`authApplierV3.Apply`'s refusal, at any index). -/
theorem kvEntryOn_adminRefused (c₀ : w64) (ch : apply.Chain) (s : OnState)
    (m : EntryModel) (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (ha : apply.needAdminPermission rq = true)
    (hok : ¬ auth.adminOk s.1 (some (auth.authInfoM (apply.principalOf rq)))) :
    kvEntryOn c₀ ch s m = s := by
  unfold kvEntryOn
  rw [if_pos ⟨ht, hd⟩, hdec]
  simp only [ha, hok, not_false_eq_true, and_self, ↓reduceIte]

/-- **An entry the auth layer lets through is today's** (the auth state kept), at the table. -/
theorem kvEntryOn_of_granted (c₀ : w64) (ch : apply.Chain) (s : OnState)
    (m : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq)
    (hna : apply.needAdminPermission rq = false)
    (hg : apply.authKVKind (apply.dispatchKind rq) = true →
      kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq) :
    kvEntryOn c₀ ch s m = (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m) := by
  have hnk := adminDispatchKind_of_needAdmin_false rq hna
  unfold kvEntryOn
  split
  · rw [hdec]
    simp only [hna, hnk, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
    rw [if_neg (fun h => h.2 (hg h.1))]
  · rfl

/-- **A request the auth layer refuses keeps the state** (the auth state, the log, the table). -/
theorem kvEntryOn_of_refused (c₀ : w64) (ch : apply.Chain) (s : OnState)
    (m : EntryModel) (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hna : apply.needAdminPermission rq = false)
    (hk : apply.authKVKind (apply.dispatchKind rq) = true)
    (hr : ¬ kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq) :
    kvEntryOn c₀ ch s m = s := by
  have hnk := adminDispatchKind_of_needAdmin_false rq hna
  unfold kvEntryOn
  rw [if_pos ⟨ht, hd⟩, hdec]
  simp only [hna, hnk, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
  rw [if_pos ⟨hk, hr⟩]

/-- **No `AuthEnable` above `c₀`**: no normal entry of `A` above `c₀` decodes to a request
`dispatch` applies as `AuthEnable`. -/
def noAuthEnable (c₀ : w64) (A : List EntryModel) : Prop :=
  ∀ m ∈ A, ∀ rq, m.typ = W32 0 → m.data ≠ [] → apply.irrDecode m.data = some rq →
    uint.Z c₀ < uint.Z m.index → apply.dispatchKind rq ≠ .authEnable

/-- **An admin step other than `AuthEnable` keeps the flag** (`AuthDisable` clears it, which a
disabled state already has; the other steps write users, roles and the revision). -/
theorem adminStateR_enabled (rq : apply.IRRModel) (st st' : auth.AuthState)
    (hen : st.enabled = false) (hk : apply.dispatchKind rq ≠ .authEnable)
    (h : adminStateR rq st st') : st'.enabled = false := by
  unfold adminStateR at h
  split at h
  · split at h
    · split at h
      · rcases h with ⟨-, rfl⟩ | ⟨o, ho, rfl⟩
        · exact hen
        · simp only [auth.stepOf] at ho; subst ho
          unfold auth.userAddF; split
          · exact hen
          · split <;> exact hen
      · subst h; exact hen
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.stepOf] at ho; subst ho
        unfold auth.roleAddF; split
        · exact hen
        · split <;> exact hen
      · subst h; exact hen
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        unfold auth.userGrantRoleR at ho
        split at ho
        · subst ho; exact hen
        · split at ho
          · subst ho; exact hen
          · split at ho
            · subst ho; exact hen
            · obtain ⟨u', -, -, rfl⟩ := ho; exact hen
      · subst h; exact hen
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        unfold auth.roleGrantPermissionR at ho
        split at ho
        · subst ho; exact hen
        · split at ho
          · subst ho; exact hen
          · split at ho <;> (subst ho; exact hen)
      · subst h; exact hen
    · rename_i hk'; exact absurd hk' hk
    · -- (nomode D3) `AuthDisable` clears the flag
      obtain ⟨o, ho, rfl⟩ := h
      simp only [auth.stepOf] at ho; subst ho
      unfold auth.authDisableF
      split
      · rfl
      · exact hen
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.stepOf] at ho; subst ho
        unfold auth.userDeleteF
        (repeat' split) <;> exact hen
      · subst h; exact hen
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.stepOf] at ho; subst ho
        unfold auth.userChangePasswordF
        (repeat' split) <;> exact hen
      · subst h; exact hen
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.stepOf] at ho; subst ho
        unfold auth.userRevokeRoleF
        (repeat' split) <;> exact hen
      · subst h; exact hen
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.stepOf] at ho; subst ho
        unfold auth.roleDeleteF
        (repeat' split) <;> exact hen
      · subst h; exact hen
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        unfold auth.roleRevokePermissionR at ho
        try simp only at ho
        split at ho
        · subst ho; exact hen
        · split at ho <;> (subst ho; exact hen)
      · subst h; exact hen
    · subst h; exact hen
  · subst h; exact hen

/-- The model's admin step other than `AuthEnable` keeps a disabled flag. -/
theorem adminNext_enabled (rq : apply.IRRModel) (st : auth.AuthState) (hen : st.enabled = false)
    (hk : apply.dispatchKind rq ≠ .authEnable) : (adminNext rq st).enabled = false := by
  unfold adminNext
  split
  · rename_i hd; exact adminStateR_enabled rq st _ hen hk (Classical.choose_spec hd).1
  · exact hen

/-- **An admin kind writes nothing to the log or the table.** -/
theorem not_writeKind_of_adminDispatchKind (k : apply.ReqKind) (h : adminDispatchKind k = true) :
    ¬ writeKind k := by
  unfold writeKind; cases k <;> simp_all [adminDispatchKind]

/-- **The porting lemma** (the no-mode plan, step 4): from a disabled auth state, along a log with
no `AuthEnable` above `c₀`, the auth-aware model stays disabled and its log and table are the
auth-free model's (`kvRaftSt`): every check passes (`adminOk`, `kvGrantedL` of a disabled state),
and an admin step writes neither the log nor the table. -/
theorem kvRaftOfOn_disabled (c₀ : w64) (ch : apply.Chain) :
    ∀ (s : OnState) (A : List EntryModel), s.1.enabled = false → noAuthEnable c₀ A →
      (kvRaftOfOn c₀ ch s A).1.enabled = false ∧ (kvRaftOfOn c₀ ch s A).2 = kvRaftSt c₀ ch s.2 A
  | s, [], hen, _ => ⟨hen, rfl⟩
  | s, m :: A, hen, hA => by
    have hstep : (kvEntryOn c₀ ch s m).1.enabled = false ∧
        (kvEntryOn c₀ ch s m).2 = kvEntrySt c₀ ch s.2 m := by
      have hok : ∀ rq, auth.adminOk s.1 (some (auth.authInfoM (apply.principalOf rq))) :=
        fun _ => Or.inl hen
      unfold kvEntryOn
      split
      · rename_i hc
        split
        · rename_i rq hdec
          rw [if_neg (fun h => h.2 (hok rq))]
          split
          · rename_i ha
            refine ⟨adminNext_enabled rq s.1 hen
              (hA m List.mem_cons_self rq hc.1 hc.2 hdec ha.1), ?_⟩
            have hw : m.data = [] ∨ m.typ ≠ W32 0 ∨ ∀ rq', apply.irrDecode m.data = some rq' →
                ¬ writeKind (apply.dispatchKind rq') :=
              Or.inr (Or.inr fun rq' h => by
                rw [hdec] at h; cases h; exact not_writeKind_of_adminDispatchKind _ ha.2)
            unfold kvEntrySt
            rw [kvEntry_nonwrite c₀ ch s.2.2 s.2.1 m hw, kvTable_nonwrite c₀ ch s.2.2 m hw]
          · rw [if_neg (fun h => h.2 (kvGrantedL_of_disabled _ _ rq hen))]
            exact ⟨hen, rfl⟩
        · rename_i hdec
          refine ⟨hen, ?_⟩
          unfold kvEntrySt kvEntry kvTable
          rw [if_pos hc.1, if_neg hc.2, if_pos hc.1, if_neg hc.2, hdec]
      · exact ⟨hen, rfl⟩
    have ih := kvRaftOfOn_disabled c₀ ch (kvEntryOn c₀ ch s m) A hstep.1
      (fun m' hm' => hA m' (List.mem_cons_of_mem _ hm'))
    show (kvRaftOfOn c₀ ch (kvEntryOn c₀ ch s m) A).1.enabled = false ∧
      (kvRaftOfOn c₀ ch (kvEntryOn c₀ ch s m) A).2 = kvRaftSt c₀ ch (kvEntrySt c₀ ch s.2 m) A
    rw [← hstep.2]; exact ih

/-- **Entries that are no normal entries keep the model's log and table** (the bootstrap log's
configuration changes). -/
theorem kvRaftOfOn_conf (c₀ : w64) (ch : apply.Chain) :
    ∀ (s : OnState) (A : List EntryModel), (∀ m ∈ A, m.typ ≠ W32 0) →
      (kvRaftOfOn c₀ ch s A).2 = s.2
  | _, [], _ => rfl
  | s, m :: A, h => by
    have hm := h m (List.mem_cons_self ..)
    have hstep : kvEntryOn c₀ ch s m = (s.1, s.2) := by
      unfold kvEntryOn kvEntry kvTable
      rw [if_neg (fun hc => hm hc.1), if_neg hm, if_neg hm]
    show (kvRaftOfOn c₀ ch (kvEntryOn c₀ ch s m) A).2 = s.2
    rw [kvRaftOfOn_conf c₀ ch _ A (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')), hstep]

/-! ### The auth history along a log (the auth-mode merge's 5b, 2026-10-29) -/

/-- **An entry the mode-`on` model records in the auth history at the auth state `st`**
(`kvEntryOn`'s admin branch): a normal entry above `c₀` whose request `dispatch` applies as an
admin step (`adminDispatchKind`; D1, 2026-11-27: until then any request needing the admin
permission), whose principal `st` admits (`auth.adminOk`), and whose step changes the state (where the store's
history grows: an outcome `.next`). Any other entry keeps the state (a refused one,
`adminNext_refused`). -/
def admEntry (c₀ : w64) (st : auth.AuthState) (m : EntryModel) : Prop :=
  m.typ = W32 0 ∧ m.data ≠ [] ∧ ∃ rq, apply.irrDecode m.data = some rq ∧
    uint.Z c₀ < uint.Z m.index ∧ adminDispatchKind (apply.dispatchKind rq) = true ∧
    auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))) ∧ adminNext rq st ≠ st

/-- `kvRaftOfOn`'s step, recording the auth state after each recorded admin entry. -/
noncomputable def admStep (c₀ : w64) (ch : apply.Chain)
    (acc : OnState × List auth.AuthState) (m : EntryModel) :
    OnState × List auth.AuthState :=
  open Classical in
  (kvEntryOn c₀ ch acc.1 m,
    if admEntry c₀ acc.1.1 m then acc.2 ++ [(kvEntryOn c₀ ch acc.1 m).1] else acc.2)

/-- **The auth history along the log `A`** in the mode-`on` model from `s₀`: the start's auth
state, then the state after each recorded admin entry (`admEntry`: admitted, the state changed). -/
noncomputable def admStatesR (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) : List auth.AuthState :=
  (A.foldl (admStep c₀ ch) (s₀, [s₀.1])).2

theorem admStep_fold_fst (c₀ : w64) (ch : apply.Chain) (A : List EntryModel) :
    ∀ (acc : OnState × List auth.AuthState),
      (A.foldl (admStep c₀ ch) acc).1 = kvRaftOfOn c₀ ch acc.1 A := by
  induction A with
  | nil => intro acc; rfl
  | cons m A ih => intro acc; rw [List.foldl_cons, ih]; rfl

theorem admStep_fold_ext (c₀ : w64) (ch : apply.Chain) (A : List EntryModel) :
    ∀ (acc : OnState × List auth.AuthState),
      acc.2 <+: (A.foldl (admStep c₀ ch) acc).2 := by
  induction A with
  | nil => intro acc; exact List.prefix_refl _
  | cons m A ih =>
    intro acc
    rw [List.foldl_cons]
    refine List.IsPrefix.trans ?_ (ih _)
    unfold admStep
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

theorem admStatesR_nil (c₀ : w64) (ch : apply.Chain) (s₀ : OnState) :
    admStatesR c₀ ch s₀ [] = [s₀.1] := rfl

open Classical in
theorem admStatesR_snoc (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) (m : EntryModel) :
    admStatesR c₀ ch s₀ (A ++ [m]) =
      if admEntry c₀ (kvRaftOfOn c₀ ch s₀ A).1 m then
        admStatesR c₀ ch s₀ A ++ [(kvRaftOfOn c₀ ch s₀ (A ++ [m])).1]
      else admStatesR c₀ ch s₀ A := by
  unfold admStatesR
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, kvRaftOfOn_snoc,
    ← admStep_fold_fst c₀ ch A (s₀, [s₀.1])]
  rfl

theorem admStatesR_snoc_adm (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) (m : EntryModel) (h : admEntry c₀ (kvRaftOfOn c₀ ch s₀ A).1 m) :
    admStatesR c₀ ch s₀ (A ++ [m]) =
      admStatesR c₀ ch s₀ A ++ [(kvRaftOfOn c₀ ch s₀ (A ++ [m])).1] := by
  rw [admStatesR_snoc]; simp [h]

theorem admStatesR_snoc_other (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) (m : EntryModel) (h : ¬ admEntry c₀ (kvRaftOfOn c₀ ch s₀ A).1 m) :
    admStatesR c₀ ch s₀ (A ++ [m]) = admStatesR c₀ ch s₀ A := by
  rw [admStatesR_snoc]; simp [h]

theorem admStatesR_prefix (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A B : List EntryModel) (h : A <+: B) : admStatesR c₀ ch s₀ A <+: admStatesR c₀ ch s₀ B := by
  obtain ⟨t, rfl⟩ := h
  unfold admStatesR
  rw [List.foldl_append]
  exact admStep_fold_ext c₀ ch t _

/-- An entry not admitted as an admin step keeps the auth state (`kvEntryOn`'s other branches; a
refused admin entry, `adminNext_refused`). -/
theorem kvEntryOn_fst_of_not_adm (c₀ : w64) (ch : apply.Chain) (s : OnState)
    (m : EntryModel) (h : ¬ admEntry c₀ s.1 m) : (kvEntryOn c₀ ch s m).1 = s.1 := by
  unfold kvEntryOn
  split
  · rename_i hn
    split
    · rename_i rq hdec
      split
      · rfl
      · rename_i hr
        split
        · rename_i ha
          by_cases hok : auth.adminOk s.1 (some (auth.authInfoM (apply.principalOf rq)))
          · by_cases hne : adminNext rq s.1 = s.1
            · exact hne
            · exact absurd ⟨hn.1, hn.2, rq, hdec, ha.1, ha.2, hok, hne⟩ h
          · exact adminNext_refused rq s.1 hok
        · split <;> rfl
    · rfl
  · rfl

theorem admStep_fold_last (c₀ : w64) (ch : apply.Chain) (A : List EntryModel) :
    ∀ (acc : OnState × List auth.AuthState), acc.2.getLast? = some acc.1.1 →
      (A.foldl (admStep c₀ ch) acc).2.getLast? = some (A.foldl (admStep c₀ ch) acc).1.1 := by
  induction A with
  | nil => intro acc h; exact h
  | cons m A ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    unfold admStep
    by_cases ha : admEntry c₀ acc.1.1 m
    · simp [ha]
    · simp only [ha, if_false]
      rw [kvEntryOn_fst_of_not_adm _ _ _ _ ha]; exact h

theorem admStatesR_last (c₀ : w64) (ch : apply.Chain) (s₀ : OnState)
    (A : List EntryModel) :
    (admStatesR c₀ ch s₀ A).getLast? = some (kvRaftOfOn c₀ ch s₀ A).1 := by
  unfold admStatesR
  rw [admStep_fold_last c₀ ch A (s₀, [s₀.1]) rfl, admStep_fold_fst]

end pure

end EtcdGrove
end Perennial
