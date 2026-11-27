# No auth modes, stage N1: the model changes (2026-11-27)

The plan: `~/coordinator-notes/plans/nomode-packet.md` (local), sections 1-2 and 5. This file holds the
exact before/after text of each definition the trusted statements are written in (`kvEntryOn`,
`adminStateR`: the vocabulary of `kvInvOn`, `writeAuD` and the `*On_dist` axioms), for an
independent review. Ledger entries: `notes/specs-only/ledger.md`, 2026-11-27.

## Step 1: layering (no meaning change)

The pure part of `KVAuthModel.lean` (`outState` ... `admStatesR_last`) moved, unchanged, to
`Proof/go_etcd_io/etcd/server/v3/etcdserver/KVAuthModelDefs.lean` (a defs module that reaches no
`etcdserver.InvRequest`, so `InvRequest.lean` can import it). `admStates*` (they name `KVNames`) stay.

## Step 2: D1, `kvEntryOn` dispatches as Go does

Go (`authApplierV3.Apply`, `server/etcdserver/apply/auth.go:43-58`): `IsAdminPermitted` if
`needAdminPermission(r)` (an error returns, nothing applied), then `dispatch` of the first set field.

**Before** (`KVAuthModel.lean`):

```lean
def kvEntryOn (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel) : OnState :=
  if m.typ = W32 0 ∧ m.data ≠ [] then
    match apply.irrDecode m.data with
    | some rq =>
      if uint.Z c₀ < uint.Z m.index ∧ apply.needAdminPermission rq = true then
        (adminNext rq s.1, s.2)
      else if apply.authKVKind (apply.dispatchKind rq) = true ∧
          ¬ kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq then s
      else (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)
    | none => s
  else (s.1, kvEntry c₀ ch s.2.2 s.2.1 m, kvTable c₀ ch s.2.2 m)
```

**After** (`KVAuthModelDefs.lean`):

```lean
def adminDispatchKind : apply.ReqKind → Bool
  | .authEnable | .authDisable | .authUserAdd | .authUserDelete | .authUserChangePassword
  | .authUserGrantRole | .authUserRevokeRole | .authRoleAdd | .authRoleGrantPermission
  | .authRoleRevokePermission | .authRoleDelete | .authUserList | .authRoleList => true
  | _ => false

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
```

- The refusal is at any index: Go checks before `dispatch`, whatever `shouldApplyV3`.
- `adminDispatchKind k` is exactly "`dispatch` takes a field `needAdminPermission` reads"
  (`needAdminPermission_of_adminDispatchKind`). Requests with such a field whose first set field is
  another (a put, a cluster request, `Authenticate`, `AuthStatus`) now take that field's branch.
- On a log today's premises admit, the value is unchanged: an admitted admin request needing the
  permission is of an admin kind (`adminDispatchKind_of_adminKindOk`), and a refused admin step was
  already the identity (`adminNext_refused`).

Follow-ups of the same change (defs, not trusted vocabulary): `outcomeOn` (`KVApplyOn.lean`, the
apply thread's relation) gets the same refusal branch and admin condition; `admEntry` (the entries
recorded in the auth history) and its twin `admLE` read `adminDispatchKind (apply.dispatchKind rq) =
true` where they read `apply.needAdminPermission rq = true`.

## Step 3: D3 (the six unmodelled admin kinds), stopped

`adminStateR` is unchanged. The step functions are right (`authDisableF`, `userDeleteF`,
`userChangePasswordF`, `userRevokeRoleF`, `roleDeleteF`, `roleRevokePermissionR` agree with
`store.go`, revision bumps included, and their store specs are proved: `Spec/.../auth/authStore__*.lean`).
What is missing is their arguments: the request model `apply.IRRModel` records these six kinds as a
`Bool` (`authUserDelete`, `authUserChangePassword`, `authUserRevokeRole`, `authRoleDelete`,
`authRoleRevokePermission`; `authDisable` needs none), with no user name, role, key or range end
(`apply/InvRequest.lean:110-151`). Wiring the steps needs:

1. `IRRModel` fields with the names (as `authUserAdd`/`authRoleAdd` got in E2n/N4), and their heap
   predicates in `internalRaftRequestIs` (`presentIs` becomes a record predicate). `IRRModel` is what the
   opaque `irrDecodeRest` returns and `internalRaftRequestIs` is the vocabulary of the trust-boundary
   axioms `pbutil.MustUnmarshalMessage.wp_proof` and the `proto` IRR specs (`MarshalIRR.lean`): their
   text and meaning change, so this needs a trusted-statement review (STOP condition).
2. `apply.AdminReq`/`adminReqOf` cases for the six, and the dispatch proofs' six branches
   (`DispatchAdmin.lean:706-`, `uberApplier__dispatch.lean`, `DispatchKVL.lean`: today `absurd` from
   `adminKindOk`) over the store specs, with the `en` flag read outside `enabledMu` (as `AuthEnable`'s,
   `enabledVerdict`/`authEnableOwnR`).
3. `adminStepO`, `adminKindOk` (drop the exclusion; key bounds for the names), `authDet` (`RoleRevokePermission`
   is a relation: an unknown-type permission may match), the proposers (`InvProposer.lean`).

## Step 4: the porting lemma

`kvRaftOfOn_disabled` (`KVAuthModelDefs.lean`), generalized (no callers had used the old one):

```lean
def noAuthEnable (c₀ : w64) (A : List EntryModel) : Prop :=
  ∀ m ∈ A, ∀ rq, m.typ = W32 0 → m.data ≠ [] → apply.irrDecode m.data = some rq →
    uint.Z c₀ < uint.Z m.index → apply.dispatchKind rq ≠ .authEnable

theorem kvRaftOfOn_disabled (c₀ : w64) (ch : apply.Chain) :
    ∀ (s : OnState) (A : List EntryModel), s.1.enabled = false → noAuthEnable c₀ A →
      (kvRaftOfOn c₀ ch s A).1.enabled = false ∧ (kvRaftOfOn c₀ ch s A).2 = kvRaftSt c₀ ch s.2 A
```

It rests on `adminStateR_enabled` (every admin step but `AuthEnable`'s keeps a disabled flag). Once
D3 wires the six steps, that lemma gains their cases (`AuthDisable` sets `false`; the others write
users, roles and the revision only).
