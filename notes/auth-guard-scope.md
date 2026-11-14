# Scope: auth-guard-completeness (a refused request names why)

2026-11-14 · Scope agent for etcd-grove-81 · worktree `/shared/etcd-grove-scope-guard`, branch
`auth-guard-scope` (from lean `7c9a02aec4`) · notes only: no Lean edits, no builds. The user approved
the goal as a next step on 2026-11-14. Go evidence: run at the etcd fork pin `2eaeb872b` (an
archive of it in `/shared/tmp/auth-guard-scope/etcd-pin`), `GOWORK=off`, under the 32G cap, go1.27.1.
The tests are in `notes/auth-guard-scope/` (§4) and all pass.

## 0. Summary

- **The property.** Today the auth guards' specs say one thing: a request that passes was
  permitted. The converse would say that a refused request names a reason its class allows.
  Each reason is a fact about the request, or about the auth state no older than what the caller
  knew when it called. The contrapositive is the user's form: a request with a valid token, whose
  principal the class admits, is not refused by the guard. Per class:
  - **Authenticated:** an accepted token always passes.
  - **Admin:** a user who has the root role at every state since the caller's lower bound passes.
  - **RBAC:** a principal permitted at those states, with a current token revision, passes.
- **Most of it is already proved below the guards. The guards drop it.**
  - The store's verdicts already have refusal halves. `permVerdict`/`permVerdictFrom` refuse in a
    view of recorded states (`refusedV`). `adminVerdict` refuses only with `adminRefused`.
  - The apply layer's KV and admin checks are already exact at the latest state.
    `authOutL`/`permVerdictL_iff` and `adminVerdictL` are iffs (the auth plan's E2r-E2v).
  - What is missing:
    - the request side's converse: `AuthInfoFromCtx` gives no principal only when the context
      carries no token;
    - a refusal half in `IsAdminPermitted.specLb`;
    - the guards' and entry points' posts, which say nothing on an error beyond `applyErrIs`.
- **The goal needs no new trust in its core (G0-G4).** It changes no axiom and no trusted text. The
  token provider's contract is proved of the simple provider, and G5 (optional) strengthens it
  without new trust (§3).
- **It changes no closed statement in G0-G4.** `etcd_auth_safe`/`etcd_auth3_safe` gain a "served"
  clause only if their example programs check one (G7, decided later, §1.4).
- **The regressions:**
  - 3.6.9's admin-only `MemberList` (and `Alarm` GET) is excluded at G3, and the Go test shows
    the violation.
  - etcd-io/etcd#20757 is not excluded by any guard-level statement. The leader's guard saw a
    context with no token, a reason the converse allows. Only G6's path statement excludes it ("the
    forwarded context carries the caller's token"), and G6 is blocked on a JSON model. The Go test
    shows both halves of the forwarding at the pin, and the pre-fix refusal.
- **Estimate.**
  - Core (G0-G3: the vocabulary, the request side, the six guards and the watch check, the guarded
    entry points): about **2 to 2.5 weeks**.
  - G4 (the serializable read path, and a results-level restatement at apply): about 1 week.
  - G4L (the lease checks, after auth-on-leases): 3-4 days.
- **A finding.** A request with a valid token can be refused with `ErrUserEmpty` when it races an
  `AuthDisable`. The authenticated check reads the enabled flag twice. Recorded as
  `nonissues/etcd-auth-requireauthinfo-disable-race-user-empty.md` (fail-closed and transient,
  `blocks-proof: no`). The converse must allow it as a reason (§2.1).

## 1. The property in plain words

### 1.1 Why the reason form, and why a lower bound

The direct form, "permitted ⇒ `err = nil`", is a safety statement about the return value, so it can
be stated in Iris under partial correctness. But "permitted" must hold at the states the check reads,
and the auth state can change during the check. An admin change can revoke root between the flag read
and the user read. So the spec states the contrapositive with witnesses:

> on a refusal, the request side lacked a principal (no token in the context, or a token the
> provider refused), or recorded states at indices at least `n` refuse the principal.

Here `n` is a lower bound of the store's published index that the caller holds (`auth.authPubLbM M n`,
E3g). The bound is what makes the statement non-vacuous. Without it a refusal could cite state 0, the
boot state, in which no user exists and auth is disabled. Any refusal would then be justified.
`permVerdictFrom` (`auth/FreshCheck.lean:77`) already has this shape for the permission checks, and
the watch check and `Range` already take `authPubLbM n`.

A caller gets the positive form when no admin change happened after `n` (the history's latest index
is `n`, as in the auth examples after `SetUp`): every witness state is then the latest state, and
`refusedV_diag` (`auth/Model.lean`) or `adminRefused` contradict "permitted there". So the guard
returns `nil`.

Errors the guard does not produce stay allowed at the entry points, unchanged: raft, the read index,
timeouts, `ErrStopped`. The converse speaks only of the auth package's error variables
(`authErrVarIs`). So it states the guard's verdict, not that the request succeeds end to end.

### 1.2 Per class

The request-side reasons are common to all three classes (`reqSideWhy`, §2.1):

- `ErrUserEmpty`: the context carries no token (`auth.ctxTokenOf ctx = none`), or auth was disabled
  at a state no older than `n` (the disable race);
- `ErrInvalidAuthToken`: the context carries a token, and the provider refused it. Before G5 this
  is only "there was a token"; G5 adds "it was never issued, or it died: expired, invalidated,
  disabled".

The class-specific reasons:

- **Authenticated** (`requireAuthInfo`, the server's at `v3_server.go:1277` and the gRPC layer's at
  `api/v3rpc/auth.go:191`): no other reason. Every accepted token passes, whether its user is root,
  has roles, or has none. Rows: `MemberList`, `Status`, `Alarm` GET, and the lease rows' first check.
- **Admin** (`checkMembershipOperationPermission`, `server.go:1385`; `AuthAdmin.isPermitted`,
  `auth.go:182`; `authMaintenanceServer.isPermitted`; at apply, `authApplierV3.Apply`'s
  `needAdminPermission`): beyond the request side, `ErrUserNotFound` or `ErrPermissionDenied`, for
  a principal bound to the request's token (`principalBound`, E1) that is absent or not root at
  recorded states no older than `n` (`adminRefused`). Rows: `Compact`, `MemberAdd`/`Remove`/
  `Update`/`Promote`, `Defragment`, `Snapshot`, `Hash`, `HashKV`, `MoveLeader`, `Downgrade`,
  `Alarm` ACTIVATE/DEACTIVATE, and the auth service's admin rows at apply.
- **RBAC**: beyond the request side, a view of recorded states no older than `n` in which the
  permission check refuses (`refusedV`). In that view the principal is non-root and does not cover
  `(key, rangeEnd, op)` (for a request of the shape the cache decides), or the token's revision is
  older than the store's (`ErrAuthOldRevision`: an admin change since the token's info was made).
  The places:
  - the watch check (`isWatchPermitted`; a context with no token checks `AuthInfo{}`, refused for
    revision 0);
  - the serializable read path (`doSerialize`'s `chk`, plus its own revision re-check);
  - the apply layer: already exact (`authOutL`, §2.4);
  - the lease checks: beyond the RBAC reasons, the admin shortcut failed (`adminRefused`) and some
    key of the lease is refused, or `Revision()` differed between the check's two reads (§2.5).

### 1.3 What the converse excludes, and what it does not

- **Excluded:** an over-check that moves a row to a stronger class. Examples: 3.6.9's `MemberList`
  and `Alarm` GET (admin where the class is authenticated), an RBAC check of the wrong operation
  type, and a guard that ignores a valid token. `TestZZGuardMemberList369Regression` shows 3.6.9's
  guard refusing an authenticated user with `ErrPermissionDenied`, a reason outside the
  authenticated class.
- **Not excluded:**
  - a path that drops the token before the guard (etcd-io/etcd#20757; the leader's guard cites "no
    token", which is true of the context it saw). G6 covers it.
  - a provider that refuses live tokens (until G5).
  - TLS identities (D-AU6): `ErrUserEmpty`'s reason is "no token". The converse does not say
    that a client certificate's common name would have been used.
  - liveness: a guard that never returns meets every triple.

### 1.4 The closed theorems

`etcd_auth_safe` (`examples/etcd/auth/Results.lean`) and `etcd_auth3_safe` are adequacy theorems
over example programs: the program returns 0/1/2 and does not panic. The guards' posts are internal
to their proofs. Strengthening them (G0-G4) changes no statement, and the docstrings stay true.

A clause "u's permitted requests succeed" has to be checked by the program, and the proof then shows
the check never fails. Suppose `Work` returns a new code 3 when a request that `permittedK` admits
fails with `ErrGRPCPermissionDenied` or `ErrGRPCUserEmpty`, and the theorem excludes 3. That takes:

1. the auth history frozen after `SetUp`, which holds in the example (root's authority, no admin
   step in the workload);
2. the KV apply path's exact outcome carried to the client's reply: `outcomeOn` exists, but
   whether the server's reply states it needs checking (G0);
3. the serializable reads' converse (G4);
4. the tokens: the simple provider's TTL keeper may delete a token at any time in the model, which
   has no clock. So `ErrInvalidAuthToken` must stay allowed (the client re-authenticates through an
   unverified retry). `ErrAuthOldRevision` can be excluded only with G5's "the info's revision is
   the store's".

The docstring line "`u`'s permitted requests need not succeed" would become "are never refused for
permission (they may still fail with a timeout, a network error or an expired token)". This is
stage **G7**. I recommend deciding it after auth3-a2 lands: auth3-a2 is changing `Work` and the
drivers now, and the clause would be cheaper on auth3's final driver.

## 2. Which specs change (draft statements)

The vocabulary goes in a new module, `Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthWhy.lean`,
which imports `AuthBound.lean`. Each guard's existing outcome predicate is kept, and a `C` variant
adds the refusal conjunct (`authedOutC := authedOutB ∗ why`), so a caller that does not need the
reason drops it with one lemma. Changing the arity of `authedOutB`/`adminOutB` would instead ripple
into the lease specs (§6).

### 2.1 Vocabulary (G0)

```lean
/-- No principal from the request side, seen with the lower bound `n`: the context carries no token,
or auth was disabled at a state no older than `n` (the store's own flag read, `store.go:1073`;
nonissues/etcd-auth-requireauthinfo-disable-race-user-empty.md). -/
def noPrincipalWhy (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) : IProp GF :=
  iprop(⌜auth.ctxTokenOf ctx = none⌝ ∨ auth.enabledVerdictFrom M n false)

/-- The context's token was refused (until G5: only that there was one). -/
def tokRefusedWhy (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) : IProp GF :=
  iprop(∃ t : GoString, ⌜auth.ctxTokenOf ctx = some t⌝ ∗ auth.tokRefusedFrom M n t)  -- G5; `True` before

def reqSideWhy (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  iprop((auth.authErrOf .userEmpty err ∗ noPrincipalWhy M n ctx) ∨
    (auth.authErrOf .invalidAuthToken err ∗ tokRefusedWhy M n ctx))

/-- `adminRefused` at states no older than `n`. -/
def auth.adminRefusedFrom (γa : auth.AuthNames) (n : Nat) (ai : Option auth.AuthInfoM) : IProp GF :=
  iprop(∃ (i j : Nat) (sf su : auth.AuthState), auth.authStateAt γa i sf ∗ auth.authStateAt γa j su ∗
    ⌜n ≤ i ∧ n ≤ j ∧ auth.adminRefused sf su ai⌝)

def authedWhy (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  match M with | .on _ => reqSideWhy M n ctx err | _ => iprop(True)

def adminWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n ctx err ∨
      ((auth.authErrOf .userNotFound err ∨ auth.authErrOf .permissionDenied err) ∗
        ∃ info, principalBound s M ctx (some info) ∗
          auth.adminRefusedFrom γa n (some (auth.authInfoM info))))
  | _ => iprop(True)

/-- One permission check `(key, rangeEnd, op)` of the auth info `info` the request side gave
(`AuthInfo{}` exactly when it gave none). -/
def permWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) (info : AuthInfo)
    (key rangeEnd : GoString) (op : auth.PermType) : IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n ctx err ∨
      (((⌜info = default⌝ ∗ noPrincipalWhy M n ctx) ∨ principalBound s M ctx (some info)) ∗
        ∃ v, auth.recordedVFrom γa n v ∗ ⌜auth.refusedV v (auth.authInfoM info) key rangeEnd op⌝))
  | _ => iprop(True)

def authedOutC (s M n ctx err) := iprop(authedOutB s M ctx err ∗ (∀ _ : err ≠ GoInterface.nil, authedWhy M n ctx err))
def adminOutC  (s M n ctx err) := iprop(adminOutB  s M ctx err ∗ (∀ _ : err ≠ GoInterface.nil, adminWhy s M n ctx err))
```

Also in G0, lemmas and checks:

- the auth error variables are pairwise distinct, by their messages (`errVarCells` over
  `authErrMsgs`, `auth/Init.lean:254`), so `authedWhy` excludes `ErrPermissionDenied`;
- `served_of_frozen`: with the history's last index `≤ n` and the principal admin, or permitted with
  a current revision, at the latest state, `adminWhy`/`permWhy` give `False` beyond the request side;
- that `LinearizableReadNotify`'s and `raftRequest`'s errors are not auth error variables (needed at
  G3), and that `togRPCError` of an auth variable is the map's value (`grpcErrOut`'s middle case
  stated precisely). If either is missing, its spec gets a post conjunct: a strengthening of a
  proved spec.

### 2.2 The request side and the store (G1)

| spec / definition | file:line | change |
|---|---|---|
| `auth.authStore.AuthInfoFromCtx.spec` | `Spec/go_etcd_io/etcd/server/v3/auth/authStore__AuthInfoFromCtx.lean:28-35` | a `specLb` beside it (premise `authPubLbM M n`): post adds `⌜a = null⌝ ∗ ⌜err = nil⌝ → noPrincipalWhy M n ctx`, and `err ≠ nil → ∃ t, ⌜ctxTokenOf ctx = some t⌝` |
| `auth.authStore.IsAdminPermitted.specLb` | `Proof/go_etcd_io/etcd/server/v3/auth/FreshAdmin.lean:117-125` | post: `adminVerdictFrom` plus a refusal half (`err ≠ nil → adminRefusedFrom γa n …`); a `nil` auth info covered (the guards call it on `AuthInfoFromCtx`'s `nil`) |
| `auth.adminVerdictFrom` | `FreshAdmin.lean:40-46` | gains the refusal half (its users are the lease checks, which ignore it) |
| `authStoreLbM` | `Proof/.../etcdserver/StoreLatest.lean:78-82` | a third row, `isAuthStoreGuardLb st RD M n`: the store's `AuthInfoFromCtx.specLb` and `IsAdminPermitted.specLb` as contracts; produced in `AuthSrv.lean` from `authInv`, beside the range and lease rows |
| `EtcdServer.AuthInfoFromCtx.spec` | `Spec/.../etcdserver/EtcdServer__AuthInfoFromCtx.lean:40-52` | premises `srvAuthLb s E ∗ □ authPubLbM M n` (optional, as a `specLb` beside it); post adds `□ (⌜M.isOn⌝ → ⌜a = null ∧ err = nil⌝ → noPrincipalWhy M n ctx)` and the token-present clause. The TLS branch keeps `a = null` only when the store gave `(nil, nil)` |

Drafts:

```lean
-- authStore__AuthInfoFromCtx.lean, beside `spec`
abbrev auth.authStore.AuthInfoFromCtx.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (ctx : GoInterfaceOk),
  {{ isPkgInit … ∗ authInv st R M ∗ enabledRd st M ∗ metadata.incomingCtxOk ctx ∗ tpReady M ∗
      auth.ctxDoneRecv ctx ∗ authPubLbM M n }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthInfoFromCtx")) (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); enabledRd st M ∗ authInfoRO a ∗ authErrIs err ∗
      ctxBound M (GoInterface.ok ctx) a ∗
      (∀ _ : a = null ∧ err = GoInterface.nil, noPrincipalWhyA M n (GoInterface.ok ctx)) ∗
      ⌜err ≠ GoInterface.nil → ∃ t, auth.ctxTokenOf (GoInterface.ok ctx) = some t⌝ }}

-- FreshAdmin.lean
abbrev auth.authStore.IsAdminPermitted.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (a : Loc) (oinfo : Option AuthInfo) (dq : DFrac),
  {{ isPkgInit … ∗ authInv st R M ∗ authRd st R M ∗ authInfoAt a dq oinfo ∗ authPubLbM M n }}  -- `a = null` for `none`
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAdminPermitted")) (Val #a))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ authInfoAt a dq oinfo ∗ authErrIs err ∗
      auth.adminVerdictFrom M n oinfo err }}   -- now with `err ≠ nil → adminRefusedFrom γa n (oinfo.map authInfoM)`
```

Callers:

- of the store's `AuthInfoFromCtx.spec`: `AuthReqDerive.lean` (`isReqAuthBound_of_authInv`),
  `AuthBound.lean`, `AuthApplyOn.lean`, `AuthSrv.lean`. They keep `spec`, and `specLb` is new.
- of `IsAdminPermitted.specLb`: `AuthLeaseLb.lean`, `AuthSrv.lean`, `etcdserver/Results.lean`.
- of `EtcdServer.AuthInfoFromCtx.spec`:
  - the six guards, `isWatchPermitted`, `doSerialize`, `processInternalRaftRequestOnce`, `ReqOn.lean`;
  - the three lease checks, which belong to the auth-on-leases Scope (§6).

The post is strengthened. The one new premise, `srvAuthLb ∗ authPubLbM n`, is taken only by the Lb
form, so every existing caller keeps the form it uses.

### 2.3 The guards (G2)

| spec | file:line | change |
|---|---|---|
| `EtcdServer.requireAuthInfo.spec` | `Spec/.../etcdserver/EtcdServer__requireAuthInfo.lean:40-47` | `(n : Nat)`, premises `srvAuthLb s E ∗ □ auth.authPubLbM E.authMode n`; post `authedOutC s E.authMode n ctx err` |
| `EtcdServer.checkMembershipOperationPermission.spec` | `Spec/.../EtcdServer__checkMembershipOperationPermission.lean:39-45` | the same, with post `adminOutC` |
| `v3rpc.AuthAdmin.requireAuthInfo.spec` | `Spec/.../api/v3rpc/AuthAdmin__requireAuthInfo.lean:39-47` | as `requireAuthInfo` |
| `v3rpc.AuthAdmin.isPermitted.spec` | `Spec/.../api/v3rpc/AuthAdmin__isPermitted.lean:38-46` | as the admin guard |
| `v3rpc.authMaintenanceServer.requireAuthInfo.spec` | `…/authMaintenanceServer__requireAuthInfo.lean:35-44` | as `requireAuthInfo` |
| `v3rpc.authMaintenanceServer.isPermitted.spec` | `…/authMaintenanceServer__isPermitted.lean:32-42` | post `adminOut` becomes `adminOutC` (today it drops even the binding `adminOutB` gives) |
| `v3rpc.serverWatchStream.isWatchPermitted.spec` | `…/serverWatchStream__isWatchPermitted.lean:44-66` | post adds `∀ _ : err ≠ nil, ∃ info, permWhy r.srv.s M n (GoInterface.ok ci) err info k e .read`. It already takes `srvAuthLb` and `authPubLbM n`: a pure strengthening |

Draft (the template for all six guards):

```lean
abbrev EtcdServer.requireAuthInfo.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAuthLb s E ∗ □ auth.authPubLbM E.authMode n ∗
      mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗ E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"requireAuthInfo")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ authedOutC s E.authMode n (GoInterface.ok ctx) err ∗
      authErrVarIs err }}
```

**Strengthening, exactly.** The posts are strengthened. Two premises are added:

- `srvAuthLb s E` is `True` with auth off (`srvAuthLb_off`); with auth on, every entry point takes
  it as `Range.spec` and the lease specs already do.
- `authPubLbM n` holds at `n = 0` by an update (`authPubLbM_zero`).

So the old triple follows from the new one for any caller that has `srvAuthLb`.

Callers (all names-only upstream, none in a closed theorem's proof; checked with `grep` of the
`Proof` tree):

- `requireAuthInfo`: `EtcdServer.{MemberList, LeaseGrant, LeaseRevoke, LeaseTimeToLive}`;
- `checkMembershipOperationPermission`: `EtcdServer.RemoveMember`;
- `AuthAdmin.isPermitted`: `kvServer.Compact`, `authMaintenanceServer.isPermitted`;
- `AuthAdmin.requireAuthInfo`: `authMaintenanceServer.requireAuthInfo`;
- `ams.isPermitted`: `ams.{Defragment, Snapshot, Hash, HashKV, MoveLeader, Downgrade, Alarm}`;
- `ams.requireAuthInfo`: `ams.{Status, Alarm}`;
- `isWatchPermitted`: `serverWatchStream.recvLoop`, which reaches the closed theorems. Its post
  only gains a conjunct, which `recvLoop` drops, so no closed statement moves.

### 2.4 The guarded entry points (G3)

Each one's error branch gains the class's reason for an auth error.
`guardOut` (`v3rpc/InvAuthAdmin.lean:140`) gets a `C` variant:

```lean
def guardOutC (Pin : IProp GF) (Q : Loc → GoInterface → IProp GF) (W : GoInterface → IProp GF)
    (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(Q resp err ∨ (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ Pin ∗
    ∃ e0, W e0 ∗ ⌜err = togRPCErrorOf e0⌝))   -- W := authedWhy … / adminWhy … ; the guard's error before togRPCError
```

| entry point | file:line | class |
|---|---|---|
| `EtcdServer.MemberList.spec` | `Spec/.../EtcdServer__MemberList.lean:37-53` | authenticated: `∀ _ : err ≠ nil, authErrVarIs err -∗ authedWhy E.authMode n ctx err` (the read notify's errors are not auth variables, G0) |
| `EtcdServer.RemoveMember.spec` | `Spec/.../EtcdServer__RemoveMember.lean:37-49` | admin, the same shape |
| `v3rpc.kvServer.Compact.spec` | `Spec/.../api/v3rpc/kvServer__Compact.lean:36-50` | admin, through `compactOut`'s guard branch |
| `v3rpc.authMaintenanceServer.{Defragment, Hash, HashKV, MoveLeader, Downgrade}.spec`, `Snapshot` (`guardOut1`) | `…/authMaintenanceServer__*.lean` | admin, `guardOutC` |
| `v3rpc.authMaintenanceServer.Status.spec` | `…/authMaintenanceServer__Status.lean` | authenticated |
| `v3rpc.authMaintenanceServer.Alarm.spec` | `…/authMaintenanceServer__Alarm.lean` | `W := if act = GET then authedWhy else adminWhy` (as `alarmTok`, `InvAuthAdmin.lean:134`) |

These are exported, linked results with no caller in a proof. Each one's post is strengthened, and
each gains `srvAuthLb s E` and `n`. `MemberAdd`, `MemberUpdate` and `MemberPromote` have only the
guard's theorem (`encoding/json`), so they get the guard's converse and no entry-point statement
until G6.

### 2.5 RBAC on the read path, at apply, and in the lease checks (G4, G4L)

- **`EtcdServer.doSerialize.spec`** (`Spec/.../EtcdServer__doSerialize.lean:47-66`):
  - a refusal predicate `R : AuthInfo → GoInterface → IProp GF` beside `C`, in the `chk`
    contract's post (`∀ _ : err ≠ nil, R info err`);
  - its error branch adds `(∃ info, R info err ∗ infoBoundM …) ∨ reqSideWhy … ∨ revChangedFrom M n info`,
    the last for its own `ErrAuthOldRevision` re-check (a revision read no older than `n`, above
    the info's);
  - `R := fun _ _ => True` recovers today's triple. Callers: `EtcdServer.{Range, Txn}` and
    `RangeStream`, which pass `R := permWhy …` of their keys.
- **Apply:**
  - Already exact: `apply.authOutL` (`apply/AuthApplyLatest.lean:47`, rejection iff `refusedL` at
    the latest state) and `auth.adminVerdictL` (`auth/LatestAdmin.lean:32`, an iff).
  - The class-track specs (`checkPutAuth`, `checkTxnReqsPermission`, `authApplierV3.*`'s
    `rejected`) need no change: the latest track subsumes them.
  - G4 adds one results-level statement in `apply/Results.lean` and `etcdserver/Results.lean`: an
    admin request's `rejectResultIs` at apply names `adminRefused` at the latest state, and a KV
    request's `.rejected .auth` names `refusedL`.
  - Plus the G0 check of whether the dispatch-level `outcomeOn` reaches the reply (for G7).
- **The lease checks** (`EtcdServer__checkLease{Renew,TimeToLive,Leases}.lean`; `LeaseCheck.lean`'s
  `leaseCheckFrom`):
  - the error branch adds `reqSideWhy ∨ (adminRefusedFrom γa n info ∗ some key's permWhy at
    lessor index ≥ m) ∨ revChangedFrom` (the re-check `rev != s.AuthStore().Revision()`,
    `v3_server.go:601`, 779);
  - the docstring's "margin" stays as it is: the converse needs no single state;
  - **G4L, after auth-on-leases lands** (§6).

## 3. Trusted text

None in G0-G4, and none in G5-G7.

- **Axioms:**
  - `auth.authStore.AuthInfoFromTLS.wp_proof` is untouched. The converse is silent on TLS (§1.3).
  - `auth.NewAuthStore.wp_proof` (mode off; `isReqAuth`) is untouched. In `off` and `any` the why
    predicates are `True`, and the auth-on server's store comes from the proved
    `newAuthStore_boot`.
  - `newTokenProviderJWT.wp_proof` states nothing of the contract, so it is untouched.
  - `tokenSimple.genTokenPrefix.wp_proof` is untouched.
- **The token provider's contract** (`tokenProviderOk`/`tokenProviderOkA`,
  `auth/InvAuth.lean:748,777`) is a definition, not trusted. It is proved of the simple provider
  (`tokenSimple_okA_run`, used in `AuthSrv.lean:717`) and of the no-op one (`TokenNop.lean`).
  G0-G4 leave it unchanged. G5 would strengthen `info`'s post on `ok = false` to
  `tokRefusedFrom M n token`: the token was never issued (`¬ ∃ u, tokIssued γa token u`), or it is
  dead (a new persistent ghost fact set by the keeper's delete, `invalidateUser` and `disable`), or
  the context was done during the index wait. On `ok = true`, G5 adds `Revision' = rev`. That
  re-proves `TokenSimple.lean`, `TokenSimpleAdmin.lean` and `TokenKeeperRun.lean` (the keeper's
  delete marks the token dead under the provider's mutex) and `TokenNop.lean` (it issues nothing,
  so every token is "never issued"). No new trust: the keeper's expiry is already modelled by
  `time.Now`'s nondeterminism, and the ghost update rides on the existing delete.
- **The context and metadata models** (`metadata.incomingOf`, `ctxTokenOf`): the converse rests on
  the same reading the binding (E2c) already rests on. No new assumption.

So no stage needs a hard stop for trust. G5 changes a proved contract (an internal definition): a
"stronger post on a proved spec", but on a definition the auth-on server's construction holds, so I
list it as a decision (D3).

## 4. Go evidence (the pin `2eaeb872b`; all pass)

Each file says where to copy it and how to run it. Each test builds the real auth store (simple
tokens, `bcrypt.MinCost`) on a temporary backend and issues tokens as the apply thread does (index
and prefix).

| test | class | what it shows |
|---|---|---|
| `zz_guard_etcdserver_test.go` `TestZZGuardAuthenticated` | authenticated | `requireAuthInfo` passes root's, `u`'s (roles) and `v`'s (none) tokens; refuses only no token (`ErrUserEmpty`) and a token never issued (`ErrInvalidAuthToken`); never refuses with auth off |
| `TestZZGuardAdmin` | admin | `checkMembershipOperationPermission`: root passes; `u` gets `ErrPermissionDenied`, no token `ErrUserEmpty`, a bad token `ErrInvalidAuthToken`; a user granted root afterwards passes |
| `TestZZGuardMemberList369Regression` | the 3.6.9 regression | `u`'s token is accepted (`AuthInfoFromCtx` gives `u`) and today's guard passes it; 3.6.9's guard (`checkMembershipOperationPermission`) refuses it with `ErrPermissionDenied`, a reason outside the authenticated class: the converse fails |
| `TestZZGuardLeaseChecks` | RBAC (leases) | `checkLeaseRenew`/`TimeToLive`/`Leases` pass `u` for a lease holding a key it may write and read, and root for any lease; refuse `u` with `ErrPermissionDenied` for a lease holding a key it may not; a missing lease passes |
| `TestZZGuardPromoteForwardsToken` | #20757, follower half | `promoteMemberHTTP` puts the gRPC context's token in `Authorization` (the fix `37531e62f`) |
| `zz_guard_promote_test.go` `TestZZGuardPromoteLeader` | #20757, leader half | the peer handler turns `Authorization` back into metadata, and the leader's admin guard passes root; the pre-fix handler's context (no metadata) gets `ErrUserEmpty`: a refusal the guard's converse allows, so only G6's path statement excludes #20757 |
| `zz_guard_v3rpc_test.go` `TestZZGuardAuthAdmin` | authenticated, admin (gRPC layer) | `AuthAdmin.requireAuthInfo` and `isPermitted` as above; `togRPCError` maps each auth error to its own gRPC error (the reason survives to the client) |
| `TestZZGuardWatch` | RBAC (watch) | `isWatchPermitted` passes a point, the exact range, a sub-range, and root's open-ended range; refuses a range beyond the grant, a write-only key, a user with no role, and no token (`ErrUserEmpty`) |
| `zz_guard_apply_test.go` `TestZZGuardApplyRBAC` | RBAC and admin at apply | `authApplierV3.Put` (with `PrevKv` and a lease whose key `u` may write), `Range`, `DeleteRange` (with `PrevKv`), a `Txn` with a nested `Txn` in the failure branch all pass for `u`; refusals: a read-only key's put, a range past the grant, an older header revision (`ErrAuthOldRevision`), no principal (`ErrUserEmpty`); `Apply` of `UserAdd` passes root's header and refuses `u`'s |

The disable race (the nonissue) has no test: it needs an interleaving inside `requireAuthInfo`.

## 5. Stages, hard stops, estimates

| stage | content | estimate | hard stop at the end |
|---|---|---|---|
| G0 | `AuthWhy.lean` (§2.1), distinctness of the auth errors, `served_of_frozen`; the checks: read-notify and raft errors are not auth variables, `togRPCError` of an auth variable, whether `outcomeOn` reaches the reply | 1-2 days | none (internal), checkpoint report |
| G1 | the request side and the store (§2.2): `AuthInfoFromCtx.specLb` (store and server), `IsAdminPermitted.specLb` refusal half with `nil`, `authStoreLbM`'s third row and its producer in `AuthSrv.lean` | 3-4 days | none (internal, proved specs strengthened), checkpoint |
| G2 | the six guards and `isWatchPermitted` (§2.3); interfaces regenerated | 3-4 days | **yes**: exported guard specs gain premises (`srvAuthLb`, `n`); the interface diff for review |
| G3 | the guarded entry points (§2.4) | 3-5 days | **yes**: exported entry-point specs |
| G4 | `doSerialize`'s `R`, `Range`/`Txn`/`RangeStream`; the apply results-level statements | ~1 week | **yes** (exported `Range`/`Txn` posts) |
| G4L | the lease checks and the lease entry points | 3-4 days | **yes**; only after auth-on-leases lands |
| G5 (optional) | token liveness in the provider's contract (§3) | 1-1.5 weeks | **yes** (D3) |
| G6 (blocked) | the forwarded promotion: translate `promoteMember`/`PromoteMember`/`promoteMemberHTTP` and `etcdhttp`'s handler; "the leader's guard context carries the caller's token" (an `isContext` law over `Authorization`) | ~2 weeks after a JSON model (`notes/perennial-changes.md`) | yes |
| G7 (decide later) | the "served" clause in `etcd_auth_safe`/`etcd_auth3_safe` (§1.4) | 1-2 weeks, after auth3-a2 | **yes**: closed statements |

Core G0-G3: about 2 to 2.5 weeks. With G4 and G4L: about 3.5 weeks. Build cost: G1's
`authStoreLbM` row rebuilds the importers of `StoreLatest.lean` (`etc/importers.py --count`
before starting). The guards' and entry points' files are leaves.

## 6. Overlap with ongoing work

- **auth-on-leases** (`/shared/etcd-grove-scope-lease`, branch `auth-lease-scope`; Scope in
  progress, only its Go tests written so far). The files both Scopes would touch:
  - `Spec/.../etcdserver/EtcdServer__checkLease{Renew,TimeToLive,Leases}.lean`;
  - `EtcdServer__Lease{Grant,Revoke,TimeToLive,Leases,Renew}.lean` (`requireAuthInfo`'s callers);
  - `Proof/.../etcdserver/LeaseCheck.lean` (`srvAuthLeaseLb`, `leaseCheckFrom`) and
    `AuthLeaseLb.lean` (`isAuthStoreLeaseLb`, `adminVerdictFrom`);
  - `auth/FreshAdmin.lean` (G1's refusal half: the lease checks consume `adminVerdictFrom`);
  - `StoreLatest.lean` (`authStoreLbM`) and `AuthSrv.lean` (its producer), if auth-on-leases
    changes the lease row;
  - `apply/checkLeasePuts.lean`, `checkPutAuth.lean`, if it threads `reqLeaseClass` (this Scope
    does not change them).

  Proposal: auth-on-leases goes first on the lease files. G1's `FreshAdmin.lean` change is
  additive (a refusal half its users drop), so it can land before or after. G4L waits for
  auth-on-leases.
- **Restart S7** (etcdstart, `NewServer`): no shared files expected. G1 touches `AuthSrv.lean`, the
  auth-on store's construction for the server. If S7 changes the auth-on boot it uses
  (`newAuthStore_boot`), `AuthSrv.lean` is shared. To check with S7's agent before G1.
- **k8s 7f-5** (the k8s etcd3 store, the client watch; its 7f-3b v3rpc part is in progress):
  `serverWatchStream__isWatchPermitted.lean`/`serverWatchStream__recvLoop.lean` may be shared if
  7f-3b touches the server's watch stream. G2 puts `isWatchPermitted` last, after 7f-3b lands.
- **The http-boundary fix** (`Proof/net/http`, rafthttp): no shared files. G6 would share
  `net/http` once it starts.
- **auth3-a2** (`/shared/etcd-grove-auth3`): no shared files in G0-G4. G7 would change its driver
  and theorem, so G7 waits for it.

## 7. Decisions needed

- **D1, the statement form.** Recommendation: the reason form with witnesses no older than the
  caller's lower bound `n` (§1.1), as `C` variants of the outcome predicates beside today's.
  Alternative: "permitted at every state from `n` ⇒ `nil`", which is equivalent for a frozen
  history but awkward to establish under concurrent admin changes.
- **D2, the new premises on exported guard and entry-point specs** (`srvAuthLb s E`, `n` with
  `authPubLbM n`). Recommendation: accept. They follow the `Range`/lease/watch precedent, are
  `True` or derivable with auth off and at `n = 0`, and no current caller is in a closed theorem's
  proof. Hard stop at G2/G3 with the interface diff.
- **D3, G5 (token liveness).** Recommendation: do it after G3, as a separate decision. It needs no
  new trust, but it strengthens the provider's contract, which the auth-on server's construction
  holds. Without it, `ErrInvalidAuthToken`'s reason is only "the context had a token".
- **D4, TLS.** Recommendation: keep it out (D-AU6). `ErrUserEmpty`'s reason is "no token", silent
  on certificate identities.
- **D5, order with auth-on-leases.** Recommendation: auth-on-leases owns the lease files first; G4L
  follows it. G0-G3 and G4 do not wait.
- **D6, G7 (the closed theorems' "served" clause).** Recommendation: decide after auth3-a2 lands;
  until then the docstrings' "need not succeed" stays true.
- **D7, G6.** Recommendation: record only. It stays blocked on the JSON model, which is
  `notes/perennial-changes.md`'s existing entry.
- **D8, the nonissue** (`nonissues/etcd-auth-requireauthinfo-disable-race-user-empty.md`, committed
  on this branch). Recommendation: keep it as a non-issue (fail-closed, transient, no test); do not
  report it upstream.

## 8. Evidence index

- Go tests: `notes/auth-guard-scope/zz_guard_{etcdserver,v3rpc,apply,promote}_test.go`, at
  `2eaeb872b` (archive `/shared/tmp/auth-guard-scope/etcd-pin`), run
  `GOWORK=off go test ./etcdserver/ ./etcdserver/apply/ ./etcdserver/api/v3rpc/ ./etcdserver/api/etcdhttp/ -run TestZZGuard -v`
  in `server/`: 9 tests pass.
- Code at the pin:
  - `server/etcdserver/v3_server.go`: 1206-1216 (`AuthInfoFromCtx`), 1277-1291
    (`requireAuthInfo`), 574-605, 607-634, 751-783 (the lease checks);
  - `server/etcdserver/server.go:1385-1404` (`checkMembershipOperationPermission`), 1693-1704
    (`MemberList`);
  - `server/etcdserver/api/v3rpc/auth.go:182-205`;
  - `server/etcdserver/api/v3rpc/watch.go:239-249`;
  - `server/etcdserver/api/v3rpc/maintenance.go:335-402`;
  - `server/etcdserver/apply/auth.go:43-63` (`Apply`), 73-94 (`checkPutAuth`);
  - `server/auth/store.go:862-936` (`isOpPermitted`, `IsAdminPermitted`), 1072-1100
    (`AuthInfoFromCtx`);
  - `server/auth/simple_token.go` (`info`, `isValidSimpleToken`);
  - `server/etcdserver/cluster_util.go:295-320` and `api/etcdhttp/peer.go:149-172` (the forwarded
    promotion).
- The store's existing refusal halves: `auth/Model.lean` (`refusedV`, `adminRefused`,
  `permVerdict`, `adminVerdict`, `refusedV_diag`), `auth/FreshCheck.lean` (`permVerdictFrom`),
  `auth/Latest.lean` (`permVerdictL_iff`), `auth/LatestAdmin.lean` (`adminVerdictL`),
  `apply/AuthApplyLatest.lean` (`authOutL`).
