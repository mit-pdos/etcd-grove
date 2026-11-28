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

## Step 3, second attempt (D3 approved, 2026-11-27): stopped at `RoleRevokePermission`

Not started on the code: one kind's Go behaviour is not a function of the model's state, which the
approved design needs (`authDet`, `detLogOn`'s premise of every committed admin entry).

- `RoleGrantPermission` stores a permission of any `PermType` (`store.go`: `PermType: r.Perm.PermType`,
  no check; proto3 enums are open, the gRPC handlers and `EtcdServer.RoleGrantPermission` pass it on).
  The model drops one of an unknown type (`permOfWire = none`, `RoleRec.toRole`, `grantPerms`), and
  `adminKindOk` admits such a grant (it bounds the name only).
- `RoleRevokePermission(r, k, e)` compares the record's permissions, the unknown-typed ones included:
  after `RoleGrantPermission(r, {k, e, PermType 7})` it succeeds and bumps the revision; on a role that
  never had it, it returns `ErrPermissionNotGranted`. Both roles are `r ↦ []` in the model. So
  `roleRevokePermissionR` (the success disjunct) is a relation at every state where no model permission
  matches, and `authDet` fails there. Measured: a Go test in `server/auth` of a fork checkout (`6b942d2`; go1.27.3) grants `{Key: "k", PermType: 7}` to one role, then `RoleRevokePermission(k)` succeeds on it (revision +1) and returns `ErrPermissionNotGranted` on a fresh role (revision kept).

The other five fit: `authDisableF`, `userDeleteF`, `userRevokeRoleF`, `roleDeleteF` agree with
`store.go` (a disabled `AuthDisable` is `.same`; `RoleDelete` rewrites only the users holding the role,
which `delRole`'s `fmap filter` equals on the state); `UserChangePassword`'s `ErrNoPasswordUser` is
determinate under a `pwSure`-like premise (`Password = ""`, `HashedPassword` a base64 encoding: what
`EtcdServer.UserChangePassword` proposes when `Password` is set), as `UserAdd`'s.

Ways out, each needing a decision:
1. The model keeps unknown-typed permissions (`Role` over `PermW`, the checks ignoring them): both steps
   become functions; the trusted vocabulary `AuthState`/`kvGranted` changes.
2. A fork fix: `RoleGrantPermission` refuses an unknown `PermType` (`ErrInvalidAuthMgmt`), with the tie
   strengthened to "every stored permission has a known type" (boot and snapshot images included);
   `roleRevokePermissionR` becomes a function. No premise; a Go change and a model change of
   `roleGrantPermissionR`.
3. `adminKindOk` admits only known-typed grants, plus the same tie strengthening: a narrower premise
   (top-level statements change).
Recommended: 2 (the Go code is the spec; an unknown permission type is enforced nowhere).

## D3: the six admin kinds modelled (2026-11-28)

Approved by the coordinator for the user (2026-11-27/28), after X-a4 made `roleRevokePermissionR` a
function (`notes/nomode-x.md`). Ledger: `notes/specs-only/ledger.md`, 2026-11-28. The step functions
(`auth/Steps.lean`) are unchanged: rechecked against `store.go` at the fork pin `18ab647b0`
(`AuthDisable` 305-324: a disabled store's is a no-op, else disabled and bumped; `UserDelete` 473-500;
`UserChangePassword` 502-545: the record rewritten with the same roles, bumped; `UserRevokeRole` 611-656;
`RoleRevokePermission` 686-722; `RoleDelete` 724-765: every user holding the role rewritten, which
`delRole`'s `fmap filter` equals on the state). Every success bumps the revision whatever the flag.

**Trusted-visible definitions: before / after.**

- `apply.IRRModel` (`apply/InvRequest.lean`). Before: `authUserDelete authUserChangePassword
  authUserRevokeRole authRoleDelete authRoleRevokePermission : Bool`. After: `authUserDelete : Option
  GoString` (the name), `authUserChangePassword : Option ChangePasswordModel` (`{ name password hashed :
  GoString }`), `authUserRevokeRole : Option (GoString × GoString)` (name, role), `authRoleDelete : Option
  GoString` (role), `authRoleRevokePermission : Option (GoString × GoString × GoString)` (role, key, range
  end). `authDisable : Bool` is unchanged (its request has no field). `ChangePasswordModel.pwSure m :=
  auth.pwSureP m.password m.hashed false` (new; `pwSureP` is `UserAdd`'s).
- `apply.dispatchKind`, `apply.needAdminPermission`, `reqTypeName`: `rq.authUserDelete` read as
  `rq.authUserDelete.isSome` (the five alike). Same meaning.
- `apply.internalRaftRequestIs` and `irrNoHdrIs` (`InvProposer.lean`). Before, the five fields:
  `irrField p go!"AuthUserDelete" (fun l => presentIs l rq.authUserDelete)` (set iff not nil). After:
  `irrField p go!"AuthUserDelete" (fun l => optReqIs l rq.authUserDelete authUserDeleteIs)`, likewise
  `authUserChangePasswordIs`, `authUserRevokeRoleIs`, `authRoleDeleteIs`, `authRoleRevokePermissionIs`
  (new): nil iff unset, else the message's fields read-only: `authUserDeleteIs r n := auth.userDeleteReqIs
  r n` (`Name`), `authUserChangePasswordIs u m` (`Name`, `Password`, `HashedPassword` at `m`'s),
  `authUserRevokeRoleIs r (n, ro) := auth.userRevokeRoleReqIs r n ro` (`Name`, `Role`),
  `authRoleDeleteIs r ro := auth.roleDeleteReqIs r ro` (`Role`), `authRoleRevokePermissionIs r (ro, k, e)
  := auth.roleRevokePermissionReqIs r ro k e` (`Role`; `Key`, `RangeEnd` slices holding `k`, `e`). So
  `pbutil.MustUnmarshalMessage.wp_proof` and `proto.MarshalIRR.spec` (text unchanged) now say the decoded
  request carries these fields, and that an encoded request decodes back to them (`irrWireOf`).
- `auth.userChangePasswordSure r` (`auth/Requests.lean`, new): the request's `Password` and
  `HashedPassword` meet `pwSureP _ _ false`.
- `adminStateR` (`KVAuthModelDefs.lean`). Before: arms for `UserAdd`, `RoleAdd`, `UserGrantRole`,
  `RoleGrantPermission`, `AuthEnable`, every other kind `st' = st`. After, added before the default:

  ```lean
  | .authDisable => authRelState (auth.stepOf (auth.authDisableF st.enabled)) st st'
  | .authUserDelete => match rq.authUserDelete with
      | some n => authRelState (auth.stepOf (auth.userDeleteF st.enabled n)) st st'
      | none => st' = st
  | .authUserChangePassword => match rq.authUserChangePassword with
      | some m => (¬ m.pwSure ∧ st' = st) ∨
          authRelState (auth.stepOf (auth.userChangePasswordF m.name)) st st'
      | none => st' = st
  | .authUserRevokeRole => match rq.authUserRevokeRole with
      | some (n, ro) => authRelState (auth.stepOf (auth.userRevokeRoleF st.enabled n ro)) st st'
      | none => st' = st
  | .authRoleDelete => match rq.authRoleDelete with
      | some ro => authRelState (auth.stepOf (auth.roleDeleteF st.enabled ro)) st st'
      | none => st' = st
  | .authRoleRevokePermission => match rq.authRoleRevokePermission with
      | some (ro, k, e) => authRelState (auth.roleRevokePermissionR ro k e) st st'
      | none => st' = st
  ```

  The admin check (`if auth.adminOk st … then … else st' = st`) is unchanged. `adminStepO` gains the same
  six (without the `¬ pwSure` disjunct). `adminNext`, `authDet` are unchanged in text.
- `apply.adminKindOk` (`apply/Chain.lean`). Before D3: the six fell to `| _ => False`, and
  `UserGrantRole`/`RoleGrantPermission` bounded the user's/role's name by `backend.maxKeySize`. After
  (the review's narrowing, see "D3, narrowed" below):

  ```lean
  | .authUserGrantRole => True
  | .authRoleGrantPermission => True
  | .authDisable => True
  | .authUserDelete => True
  | .authUserChangePassword => ∀ m, rq.authUserChangePassword = some m → m.pwSure
  | .authUserRevokeRole => True
  | .authRoleDelete => True
  | .authRoleRevokePermission => True
  ```

  `UserChangePassword`'s `pwSure` is NOT like `UserAdd`'s: `EtcdServer.UserChangePassword` forwards a
  client's `HashedPassword` as sent when `Password` is empty, so a raw gRPC client can break it (clientv3
  never sets `HashedPassword`); it is still a premise (open: "D3, narrowed").
- `EtcdServer.{UserDelete,UserRevokeRole,RoleDelete,RoleRevokePermission}.spec`: before, `⌜r ≠ null⌝` and
  the request `irrUserDelete` (a `Bool`); after, the request's model (`apply.authUserDeleteIs r name`, ...)
  and `irrUserDelete name` (`irrUserRevokeRole name role`, `irrRoleDelete role`, `irrRoleRevokePermission
  role key rangeEnd`), as `RoleAdd.spec`'s.

**The encoding.** The heap predicates name the fields the verified store proofs already read (`auth.*ReqIs`,
the Goose struct fields of `etcdserverpb`); the decoder's claim for them is protobuf's round trip of proto3
`string`/`bytes` fields inside a set message field. Measured (scratch Go test against the fork's `api`
module, protobuf-go v1.36.12, `go1.27`): each of the six set alone, with names, empty contents, and `Key:
[]byte{}`/`RangeEnd: nil`, survives `proto.Marshal`/`proto.Unmarshal` with presence and fields equal
(empty and nil `bytes` both read as `[]` in the model); a `Role` of `"\xff"` makes `Marshal` fail
(`MarshalIRR.spec`'s error arm).

**The proofs.** The store's `X.specTB` (backend kept, the flag read `= b0`) for the five, from their
`specT` proofs; `UserChangePassword.specTSureB` (no `ErrNoPasswordUser` under `userChangePasswordSure`, as
`UserAdd`'s). `isAuthStepsX` gains six clauses (the flag-reading four at `flagR`, their cap at the state's
own flag, `auth.ownFlagR`); `isAuthStepsX_of_authInvT` is now `_of_authInvTB` at `Ψ = True`
(`isAuthStepsX_wIso`). `AdminReq`, `applierAdmin_backendX`, `dispatch.adminSpec` (`DispatchAdmin.lean`),
`adminOut_model` (`ApplyTieOn.lean`), `capRel` (`AuthTie.lean`), `rolesSorted`/`authDet_of_sorted`
(`KVAuthShape.lean`; `adminDetReq` gains `UserChangePassword`'s `pwSure`, from `adminKindOk`),
`adminStateR_wf`, `adminStateR_enabled`, `adminStateR_ord` take the six.

## D3, narrowed (2026-11-28, the review rev-d3)

The review found nothing false and one NEEDS-NARROWING finding. Witness:
`notes/axiom-review/d3-gotest/` (Go, at the fork pin).

**(1) Name bounds dropped where the store only rewrites an existing record.** A 40000-byte name for
`UserChangePassword`, `UserRevokeRole`, `RoleRevokePermission` (and `UserGrantRole`,
`RoleGrantPermission`, which rewrite an existing user or role too) meets "not found": no write, no panic.
Before / after:

- `apply.adminKindOk`: before, `UserGrantRole` `∀ u ro, … → u.length ≤ maxKeySize`, `RoleGrantPermission`
  `∀ n w, … → n.length ≤ maxKeySize`, `UserChangePassword` `… → m.name.length ≤ maxKeySize ∧ m.pwSure`,
  `UserRevokeRole`/`RoleRevokePermission` the name bound; after, `True` (`UserChangePassword`: `pwSure` only).
- The store specs (`authStore.X.spec`/`specT`/`specTB`, `UserChangePassword.specTSureB`) of those five: the
  premise `⌜name.length ≤ backend.maxKeySize⌝` (the request's name) replaced by `⌜auth.userKeysOk M hs⌝`
  (UserChangePassword, UserGrantRole, UserRevokeRole) or `⌜auth.roleKeysOk M hs⌝` (RoleGrantPermission,
  RoleRevokePermission), new (`auth/Steps.lean`): every name stored at the state the batch transaction
  finds is a bbolt key (`∀ s, histLast M hs s → ∀ n, (s.users !! n).isSome → n.length ≤
  backend.maxKeySize`; roles alike), as `RoleDelete`'s premise already was. The proofs take the bound of
  the record they rewrite from it (it exists at `st0`).
- `auth.authSmall` (`auth/Fuel.lean`) gains `roleNames : ∀ r, (st.roles !! r).isSome → r.length ≤
  backend.maxKeySize`, kept by every step (`RoleAdd`'s from its request's bound, `stepSmall_roleAdd`'s new
  premise); the fuel discharges `userKeysOk`/`roleKeysOk` (`names`, `roleNames`), so the apply layer's
  `isAuthSteps(X)` clauses, `stepSpec(X)` take the stored-name premise and `fuelSpec(X)` none;
  `AdminReq.nameOk`: `userGrantRole _ ro => utf8Valid ro`, the other rewrites `True`.
- `EtcdServer.{UserGrantRole,RoleGrantPermission}.specOn` (`ModeSpecs.lean`) and `adminPropOk_*` drop the
  name premise. (`v3rpc.userGrantRole_end_to_end_on`/`roleGrantPermission_end_to_end_on` keep theirs,
  now unused: a follow-up.)

**(2) `UserChangePassword` as a function: not done, STOPPED.** Making the step a function of the state
needs, besides the user's `NoPassword` option in the model's user record, the exact outcome of
`selectPassword`: when `Password = ""` (or a hash is given), `base64.StdEncoding.DecodeString`'s error
(Perennial's `stdDecInit` gives only "an encoding decodes"; Go's non-strict decoder also skips `\r`/`\n`), and
when only `Password` is given, bcrypt's (`bcrypt.GenerateFromPassword.spec`, an axiom, allows an error on
any input; Go errs iff the password is over 72 bytes or the cost is invalid). So either (a) a Perennial
proof of `DecodeString`'s exact error and a strengthened bcrypt axiom (new trust), or a premise. The
premise `pwSure` is kept until decided.

**Decided (coordinator for Upamanyu, 2026-11-28): option (b), interim.** `pwSure` on `UserChangePassword` stays
as a premise of `adminKindOk`. It is a proof-simplifying premise the model rule (no premise that only
simplifies proofs; the model is correct for every request Go accepts) disallows: kept only until (a).
Still a strict improvement: before D3 the six kinds were excluded from logs entirely.
**Follow-up (a), owner: the dsverify-net lead.** (i) a Perennial proof of `base64.StdEncoding.DecodeString`'s
exact error (Perennial's own workflow, a branch off its `lean`); (ii) the `bcrypt.GenerateFromPassword`
axiom narrowed to Go's exact error condition (password over 72 bytes or an invalid cost), with a witness
and an axiom review; (iii) the user's `NoPassword` option in the model, `selectPassword`'s outcome exact,
the step a function; `pwSure` removed.

## D3 follow-up (a): `UserChangePassword` exact, `pwSure` removed (2026-11-28)

`UserChangePassword`'s step is now a function of the model's state and the request, and `adminKindOk`
admits every `UserChangePassword` request. Witness: `notes/axiom-review/pw-gotest/` (bcrypt's exact error,
base64's exact acceptance, the real store's outcomes against the model; all pass at the fork pin).
Ledger: `notes/specs-only/ledger.md`, 2026-11-28, "`UserChangePassword` exact".

**(i) base64: no Perennial change.** `encoding/base64` is translated with its bodies in this repository
(`Code/encoding/base64.toml`, project k8s-apiserver), its decoder proved here (`Proof/encoding/base64/`);
Perennial has nothing of the package, so the exact error is proved here, not on a Perennial branch. The
package fact, before / after:

- before: `stdDecInit`'s post `⌜(∃ x : List w8, s = stdEnc x) → err = GoInterface.nil⌝`;
- after: `⌜err = GoInterface.nil ↔ stdDecOk s⌝`, `stdDecOk s := base64.b64Ok stdAlphabet (dropNL s)`,
  `dropNL s := s.filter fun c => !(c == W8 10 || c == W8 13)` (`b64Ok`, padded base64 text, moved from
  `DecodeDefs.lean` to `Base.lean` unchanged). Proved over the translated `Decode`/`decodeQuantum`.

**(ii) bcrypt (trusted, for an independent axiom review).** `bcrypt.GenerateFromPassword.spec`, before / after:

- before: error branch `… ∗ ⌜h = slice.nil⌝`; success branch `⌜err = GoInterface.nil⌝ ∗ ∃ hs, h ↦* hs`;
- after: error branch `… ∗ ⌜h = slice.nil⌝ ∗ ⌜72 < p.length ∨ 31 < sint.Z cost⌝`; success branch
  `⌜err = GoInterface.nil⌝ ∗ ⌜p.length ≤ 72 ∧ sint.Z cost ≤ 31⌝ ∗ ∃ hs, h ↦* hs`
  (x/crypto v0.57.0: `len(password) > 72` → `ErrPasswordTooLong`; `newFromPassword` replaces a cost below
  `MinCost` by `DefaultCost` and `checkCost` refuses one above `MaxCost`; reading the salt from the default
  `crypto/rand.Reader` does not fail, as the docstring already claimed). Witness `TestBcryptExactError`.

**(iii) the model.** Before / after (trusted definitions the top-level statements are written in):

- `auth.AuthState`: gains `noPwUsers : GMap GoString Unit` (the users whose `Options.NoPassword` is set);
  `AuthState.noPw st n := (st.noPwUsers !! n).isSome`; `bootState := ⟨false, 0, ∅, ∅, ∅⟩`.
- `auth.userAddF name st` → `auth.userAddF name nob st`: the next state `bump (putUser st name [])` →
  `bump (addUser st name nob)`, `addUser st name nob := { putUser st name [] with noPwUsers := setNoPw
  st.noPwUsers name nob }`, `setNoPw m n b := if b then insert n () m else delete n m`.
- `auth.userChangePasswordF name st` (before: `none => .err .userNotFound | some _ => .next (bump st)`) →
  `auth.userChangePasswordF name ok st := match st.users !! name with | none => .err .userNotFound
  | some _ => if st.noPw name = true ∨ ok then .next (bump st) else .err .noPasswordUser`.
- New `auth.selectPwOk pw hpw := if pw ≠ [] ∧ hpw = [] then pw.length ≤ 72 else encoding.base64.stdDecOk hpw`
  (`selectPassword` at a cost ≤ 31: `authInv` keeps the bound, `NewAuthStore` clamps the cost).
- `adminStateR`'s `UserChangePassword` clause, before `(¬ m.pwSure ∧ st' = st) ∨ authRelState (stepOf
  (userChangePasswordF m.name)) st st'`, after `authRelState (stepOf (userChangePasswordF m.name (selectPwOk
  m.password m.hashed))) st st'`; its `UserAdd` clause's step `userAddF m.name m.noPassword`; `adminStepO`
  alike.
- `apply.adminKindOk`: `.authUserChangePassword => ∀ m, rq.authUserChangePassword = some m → m.pwSure`
  → `.authUserChangePassword => True`. `ChangePasswordModel.pwSure` is gone; `adminDetReq` keeps only
  `UserAdd`'s `pwSure`.

The store side: `userOut(X)`, `schema.usersAt`/`authBucketsAre` give a read record's `noPassword` as the
state's `noPw`; the batch-transaction put contract (`authBatchTxLk`, trusted at the backend realization,
proved there: `AuthRealWr.usersAt_put`) puts `putUserRec st ur` (roles and `NoPassword`), equal to
`putUser` for a rewrite that keeps the read options (`putUserRec_same`). `UserChangePassword.{spec,specT,specTB}`
(the last was `specTSureB`, which took `userChangePasswordSure`) take the request's passwords
(`userChangePasswordReqIs r name pw hpw`), step `userChangePasswordF name (selectPwOk pw hpw)`, and no extra
error (`noExtra`). `selectPassword.spec`: `err = nil ↔ selectPwOk password hashed`, its pre the cost bound.

**`UserAdd`'s `pwSure` kept.** Removing it is not needed for exactness here (the server's `UserAdd`
proposes the `pwSure` form, a workload fact discharged at the handler) and is not cheap: the set-up
examples' and the single-process/dist chains read it. Its step gains `nob` only. The authwork set-up asks
for `noPassword = false` of its `UserAdd`s (`setupReqAt`, from the client's request), so `setupSt` has no
no-password user (`noPwUsers := ∅`); `adminStateR_userAdd_sure` substitutes the server's form of a password
(empty password, `stdB64Enc []`) where it set `noPassword`.

The `NewAuthStore` axiom (mode `off`) names `apply.isAuthStore … .off`, whose `UserAdd` clause
(`authReqContractN`) takes the request predicate `auth.userAddReqIs`, now with the option as a parameter:
it passes `fun r n => ∃ nob, auth.userAddReqIs r n nob`, the predicate as it was (the option was an
existential inside); its clauses name no step, so the axiom's meaning is unchanged.
