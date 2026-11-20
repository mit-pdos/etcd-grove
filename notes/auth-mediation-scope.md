# Scope: complete mediation on etcd's client port ("access control on every client request")

2026-11-20 · Scope agent for etcd-grove-03 · worktree `/shared/etcd-grove-authmed`, branch
`auth-mediation-scope` (from lean `f7f4930794`) · notes and Go tests only: no Lean edits, no builds.
Go evidence: run at the etcd fork `6e8f0c004` (`d3feef9bc`, the pin, only adds WAL fixes; the checkout
lacks it), an archive in `/shared/tmp/authmed/etcd-pin`, `GOWORK=off`, go1.27.1, 32G cap.

## 0. Summary

- **The goal.** Prove that etcd checks access on every request path a client can reach. The paper could
  then say "access control on every client request".
- **Where it stands.** Of the 49 client-port gRPC methods of `notes/auth-matrix.md`:
  - 25 have a proved spec that carries the row's check for the request's principal, end to end. For
    the KV and lease rows it is at the server entry point or the apply chain. For the Auth service's
    15 admin rows it is at apply.
  - 2 are public.
  - 11 are proved only over an inner contract that requires the guard's token, or at the server
    entry point with the gRPC wrapper names-only (§1).
  - 4 are not proved past the guard.
  - The 7 Lock/Election rows are either broken at the pin (3, etcd-io/etcd#17502) or proved only
    over an in-process client contract that names no principal (4).
  - Outside the matrix, also on the client port: the gRPC health service (3 methods, public by
    design), the HTTP gateway `/v3/*` (it re-enters the gRPC server), and HTTP endpoints that are
    unauthenticated by design (`/health`, `/livez`, `/readyz`, `/metrics`, `/version`,
    `/debug/vars`; with options, pprof and `/debug/requests`).
- **A finding (security-sensitive)** in the HTTP gateway, kept private (etcd-grove-private).
  - **STOP: disclosure.** The file must not reach a public branch before the user decides on
    private disclosure (§5, D1).
- **Recommendation.** Two pieces, both strengthening what exists. Neither adds a twin.
  - (a) A mechanical gate (`etc/auth-mediation-check.py`, in `etc/gates.sh`). It enumerates every
    method registered on the client port, from the Go registration code and the generated service
    descriptors at the pin. It requires each method to have a row in a committed table with a status
    and a spec, against a shrink-only baseline.
  - (b) An exhaustive `v3rpc.Server.spec`, strengthened in place. The registrations become exactly
    the six services' and health's, each with its row's spec as the registration's contract. This
    gives one linking theorem, `client_port_mediated`. It needs no new effect model. The semantic
    content stays in the per-handler specs, which already carry the checks (§2).
- **Lock/Election.** Recommendation: a named exclusion now, not a premise. A fork fix plus a
  translation of the in-process client is a separate, multi-week decision (§3.1).
- **Estimate.**
  - To the honest paper line (stages M0-M3): about **2.5-3.5 weeks, 5-7 sessions, ~2.5-3.5k Lean
    lines**, 4-6 targeted builds and 2 full builds.
  - Optional: provenance (M5) adds 1.5-2 weeks; Lock/Election via a fork (M6) 3-4 weeks.

## 1. Status table, row by row

Re-derived from the code at the pin. The registration code is `v3rpc/grpc.go:84-93`
(`Server`: KV, Watch, Lease, Cluster, Auth, Health, Maintenance) and `embed/serve.go:185-188,
245-248` (Election, Lock, `cfg.ServiceRegister` (an embed hook, nil in the etcd binary)). The gateway
is `embed/serve.go:331-383`, and the HTTP mux is `embed/etcd.go:769-773` and `serve.go:398-423`. No
gRPC reflection or channelz is registered (grep of `server/`).

Legend for the status column:

- **E2E**: the handler is translated with its body, and its exported spec (at the server entry point
  or the apply chain) states the row's check for the request's principal. The gRPC wrapper carries
  it, directly or through the contract the server instantiates.
- **E2E-a**: the same, at the apply layer only. The API path proposes the entry with its header bound
  to the token (`hdrBoundM`, `ReqOn.lean:461`), and apply checks it.
- **C**: the wrapper is proved, and the effect is an inner operation taken as a contract whose
  precondition needs the guard's token (`adminRes`/`authedRes`/`alarmTok`). The inner operation is
  names-only.
- **S**: the server entry point is E2E, and the gRPC wrapper (`ClusterServer.*`, `v3rpc/member.go`)
  is names-only.
- **G**: only the guard's spec is proved.
- **N**: nothing past the request check.
- **X**: violated at the pin (an issue).

Refusal-completeness ("refusal complete") means a refused request names a reason its class allows:
the G0-G4 work. Spec and proof paths are relative to `Spec/go_etcd_io/etcd/server/v3/etcdserver/`
(`S/`) and `Proof/go_etcd_io/etcd/server/v3/etcdserver/` (`P/`). Line numbers are those of the `abbrev
….spec` and the `theorem ….wp_proof`.

| # | method | class | guard (spec · proof) | handler spec (spec · proof) | status | refusal complete | missing |
|---|---|---|---|---|---|---|---|
| 1 | KV `Range` | RBAC read | `doSerialize`'s `chk` (`S/EtcdServer__doSerialize.lean:57` · `P/…:106`) | `S/EtcdServer__Range.lean:55` · `P/…:735`; `S/api/v3rpc/kvServer__Range.lean:32` · `:33` (via `KVAns`) | E2E (API) | yes (G4: `rangeWhyOut`) | — |
| 2 | `RangeStream` | RBAC read | the same `chk`, once, before the first page | none: `kvServer.RangeStream` is translated, not proved; `EtcdServer.RangeStream` is names-only (`SpecPlan/…/EtcdServer__RangeStream.lean` only) | N | no | translation and proof (M3); the margin `issues/etcd-rangestream-auth-revoked-midstream.md` |
| 3 | `Put` | RBAC write (+read with `PrevKv`, + the lease's keys) | `apply.checkPutAuth` (`S/apply/checkPutAuth.lean:31` · `:28`) | `S/apply/authApplierV3__Put.lean:30` · `:30`; `chain_put` (`P/apply/Results.lean:220`); `S/EtcdServer__Put.lean:45` · `:42` | E2E-a | at apply: exact (`authOutL`, `kv_rejected_why`); at the proposer: accepted for KV (G4 (d)) | the dispatch does not carry `reqLeaseClass` (A1 note) |
| 4 | `DeleteRange` | RBAC write (+read) | the apply chain | `S/apply/authApplierV3__DeleteRange.lean:30`; `chain_deleteRange` (`Results.lean:272`); `S/EtcdServer__DeleteRange.lean:37` · `:42` | E2E-a | as `Put` | — |
| 5 | `Txn` | RBAC: compares read, both branches, nested | read-only: `CheckTxnAuth` in `chk` (`S/apply/CheckTxnAuth.lean:31`, `specLbW`); write: `authApplierV3.Txn` (`S/apply/authApplierV3__Txn.lean:30`) | `S/EtcdServer__Txn.lean:80` · `P/…:699`; `chain_txn` (`Results.lean:368`) | E2E / E2E-a | yes (`txnWhyOut`; at apply exact) | `txnLeaseClass` omits `putKeep` (wire `Lease` forgets it; a model detail) |
| 6 | `Compact` | admin | `AuthAdmin.isPermitted` (`S/api/v3rpc/AuthAdmin__isPermitted.lean:39` · `:31`) | `S/api/v3rpc/kvServer__Compact.lean:39` · `:34` (`compactOk` needs `adminRes`); `S/EtcdServer__Compact.lean:75` · `:207` | C | yes (G3 `adminWhy`) | checked at check time only: `nonissues/etcd-compact-admin-check-lagging-member.md`; provenance at apply (M5) |
| 7 | Watch `Watch` (per create) | RBAC read `[Key, RangeEnd)` | `isWatchPermitted` (`S/api/v3rpc/serverWatchStream__isWatchPermitted.lean:51` · `:48`) | `S/api/v3rpc/watchServer__Watch.lean:59` · `:70` (`watchAuthed` per created watcher, A4); `watch_registered_authorized` | E2E | at the check (`permWhy`); `recvLoop` drops it | no re-check of live watchers (etcd's documented behaviour) |
| 8 | Lease `LeaseGrant` | authenticated | `requireAuthInfo` (`S/EtcdServer__requireAuthInfo.lean:43`/`specC:69` · `:30`/`:189`) | `S/EtcdServer__LeaseGrant.lean:73` · `:44`; `S/api/v3rpc/LeaseServer__LeaseGrant.lean:47` · `:34` (`leaseCheckFrom`) | E2E (API) | guard only (G4L) | provenance: apply does not check (M5) |
| 9 | `LeaseRevoke` | authenticated + RBAC write of the lease's keys | `requireAuthInfo`; apply `checkLeasePuts` (`S/apply/authApplierV3__LeaseRevoke.lean:30`) | `S/EtcdServer__LeaseRevoke.lean:65` · `:43`; `chain_revoke` (`Results.lean:425`) | E2E + E2E-a | guard; at apply exact | — |
| 10 | `LeaseTimeToLive` | authenticated; admin or RBAC read of the keys | `checkLeaseTimeToLive` (`S/EtcdServer__checkLeaseTimeToLive.lean:44` · `:33`) | `S/EtcdServer__LeaseTimeToLive.lean:58` · `:38`; `S/api/v3rpc/LeaseServer__LeaseTimeToLive.lean:48` · `:41` | E2E, with a stated margin | guard only (G4L) | **X in part**: `issues/etcd-lease-timetolive-keys-toctou.md` (keys attached after the check are returned) |
| 11 | `LeaseLeases` | authenticated; admin or RBAC read of every lease's keys | `checkLeaseLeases` (`S/…:41` · `:33`) | `S/EtcdServer__LeaseLeases.lean:45` · `:44`; `S/api/v3rpc/LeaseServer__LeaseLeases.lean:41` · `:40` | E2E | guard only | the revision re-check is not stated |
| 12 | `LeaseKeepAlive` (per renewal) | authenticated; admin or RBAC write of the keys | `checkLeaseRenew` (`S/EtcdServer__checkLeaseRenew.lean:49` · `:33`) | `S/EtcdServer__LeaseRenew.lean:63` · `:425`; `S/api/v3rpc/LeaseServer__leaseKeepAlive.lean:38` · `:151` (over `raftLeaseRenew`, whose post is `renewAns`) | E2E per renewal, with a margin | guard only | margins: keys TOCTOU and follower lag (`nonissues/etcd-lease-renew-keys-follower-lag.md`, `etcd-lease-checks-lagging-member.md`); M0 checks that the stream spec keeps `renewAns` per response |
| 13 | Cluster `MemberAdd` | admin | `checkMembershipOperationPermission` (`S/EtcdServer__checkMembershipOperationPermission.lean:48` · `:31`) | none: `EtcdServer.AddMember` and `ClusterServer.MemberAdd` are names-only (`encoding/json`) | G | guard (G2) | M2 |
| 14 | `MemberRemove` | admin | the same | `S/EtcdServer__RemoveMember.lean:40` · `:30` (`adminRes`, `adminWhy`) | S | yes (G3) | the wrapper (M2); check-time TOCTOU (`server.go:1403-1408`'s own comment) |
| 15 | `MemberUpdate` | admin | the same | none (names-only) | G | guard | M2 |
| 16 | `MemberList` | authenticated | `requireAuthInfo` | `S/EtcdServer__MemberList.lean:42` · `:29` (`authedRes`, `authedWhy`) | S | yes (G3) | the wrapper (M2) |
| 17 | `MemberPromote` | admin (checked on the member, and again on the leader after forwarding with the token, #20757's fix) | the same | none (names-only); the peer handler (`etcdhttp/peer.go:143-149`) is not translated | G | guard | M2; the peer re-check (G6 of the guard Scope) |
| 18-23 | Maintenance `Defragment`, `Snapshot`, `Hash`, `HashKV`, `MoveLeader`, `Downgrade` | admin | `authMaintenanceServer.isPermitted` (`S/api/v3rpc/authMaintenanceServer__isPermitted.lean:34` · `:30`) | `S/api/v3rpc/authMaintenanceServer__<M>.lean:38` · `:33` each (inner `maintenanceServer.<M>` a contract) | C | yes (G3) | none needed for mediation (the inner effect runs only with the token); `Downgrade`'s apply provenance (M5) |
| 24 | `Alarm` | GET authenticated; ACTIVATE/DEACTIVATE admin | both guards | `S/api/v3rpc/authMaintenanceServer__Alarm.lean:39` · `:34` (`alarmTok`) | C | yes (G3) | provenance of the alarm entry (M5) |
| 25 | `Status` | authenticated | `authMaintenanceServer.requireAuthInfo` (`:35` · `:30`) | `S/api/v3rpc/authMaintenanceServer__Status.lean:38` · `:33` | C | yes | — |
| 26 | Auth `Authenticate` | public (releases a token for a correct password) | — | `S/EtcdServer__Authenticate.lean:48` · `:43` (a token issued to `name`, over `authnStoreOk`); `S/api/v3rpc/AuthServer__Authenticate.lean:34` · `:31` | public | — | the password check is the store contract's (D-AU6 scope); not a mediation row |
| 27 | `AuthStatus` | public (etcd-io/etcd#20802) | — | `S/api/v3rpc/AuthServer__AuthStatus.lean:34` · `:31` | public | — | — |
| 28-40 | `AuthEnable`, `AuthDisable`, `UserAdd`, `UserDelete`, `UserChangePassword`, `UserGrantRole`, `UserRevokeRole`, `UserList`, `RoleAdd`, `RoleDelete`, `RoleGrantPermission`, `RoleRevokePermission`, `RoleList` | admin | at apply, `authApplierV3.Apply`'s `needAdminPermission` (`S/apply/authApplierV3__Apply.lean:30` · `:29`) | wrappers `S/api/v3rpc/AuthServer__<M>.lean:34` · `:31` (`authRaftOk` contract); server entry points `S/EtcdServer__<M>.lean` (all but `UserChangePassword`, which is names-only); apply: `adminPass`, `apply_<M>_step` | E2E-a | at apply (`admin_rejected_why`); **not at the proposer** (G4 left: `adminTieAr`) | M4 |
| 41 | `UserGet` | admin or the user itself | `authApplierV3.UserGet` (`S/apply/authApplierV3__UserGet.lean:30` · `:29`) | `userGetClass`; `S/EtcdServer__UserGet.lean:35` · `:29` | E2E-a | as above | the method-level triple does not carry it (A3 note) |
| 42 | `RoleGet` | admin or a role the user has | `authApplierV3.RoleGet` (`S/apply/authApplierV3__RoleGet.lean:30` · `:29`: "unless admin or has the role, an error") | `S/EtcdServer__RoleGet.lean:35` · `:29` | E2E-a | as above | (the matrix's "not stated" is out of date) |
| 43 | Lock `Lock` | as the caller's KV, lease and watch calls | none of its own | `S/api/v3lock/lockServer__Lock.lean:39` · `:36`, over `lockClientOk` (`P/api/v3lock/Defs.lean:54`, no principal) | **X** (#17502: the waiting watch is checked as another user) | — | §3.1 |
| 44 | `Unlock` | RBAC write `Key` | through the in-process client's `Delete`, with the caller's context | `S/api/v3lock/lockServer__Unlock.lean:32` · `:28`, over `unlockKVOk` | C (over an untranslated client) | — | `v3client` and the adapter are untranslated |
| 45 | Election `Campaign` | as `Lock` | — | `S/api/v3election/electionServer__Campaign.lean:39` · `:35` | **X** (#17502) | — | §3.1 |
| 46 | `Proclaim` | RBAC write and read of the leader key | the client's `Txn` | `…/electionServer__Proclaim.lean:41` · `:32` | C (client) | — | as `Unlock` |
| 47 | `Leader` | RBAC read of the prefix | the client's `Get` | `…/electionServer__Leader.lean:39` · `:31` | C (client) | — | as `Unlock` |
| 48 | `Observe` (stream) | RBAC read of the prefix | `Get` as the caller, then `Watch` on the shared stream | none (translated, not proved) | **X** (#17502) + N | — | §3.1 |
| 49 | `Resign` | RBAC write of the leader key | the client's `Txn` | `…/electionServer__Resign.lean:40` · `:32` | C (client) | — | as `Unlock` |
| — | `grpc.health.v1.Health/{Check, List, Watch}` | public by design (serving status only) | — | grpc's library: no spec; registered in `Server` (`grpc.go:89-91`), not in the spec's lists | public | — | classify it in the table (M1); no data released |
| — | HTTP `/v3/*` gateway | each method's row (it calls the gRPC server over loopback) | the gRPC rows | not translated (`embed`) | **X**: private finding | — | excluded with TLS identities (§3.5) |
| — | HTTP `/health`, `/livez`, `/readyz`, `/metrics`, `/version`, `/debug/vars`; pprof (`--enable-pprof` or debug log level); `/debug/requests`, `/debug/events` (debug log level) | unauthenticated by design | — | not translated | out of the matrix | — | the paper line must say "gRPC request" (§4) |

**Counts (the 49 rows).**

| status | rows |
|---|---|
| E2E or E2E-a | 25 (rows 1, 3-5, 7-12, 28-42) |
| public | 2 |
| C | 9 (rows 6, 18-25) |
| S | 2 (14, 16) |
| G | 3 (13, 15, 17) |
| N | 1 (2) |
| Lock/Election | 7: X 3 (43, 45, 48), C over an untranslated client 4 |

Refusal-completeness: proved for every guard (G2), and at the entry points of rows 1, 5, 6, 14, 16,
18-25 (G3/G4). It is not proved at the lease entry points (G4L), nor at the proposer for the admin
rows (M4).

**Corrections to `notes/auth-matrix.md`** (to make in M0):

- A linearizable `Range` is not checked at apply. Every `Range`/`RangeStream` goes through
  `doSerialize`'s `chk` after the read index (`v3_server.go:138-153`). `authApplierV3.Range` is
  reached only by a raft `Range` entry, which no client path proposes.
- `Authenticate` is proved at the server (`S/EtcdServer__Authenticate.lean:48`).
- `RoleGet`'s "or a role the user has" is stated (`authApplierV3.RoleGet.spec`).
- `issues/etcd-v3lock-watch-shared-stream-principal.md` duplicates #17502. Its front matter now says
  `upstream: known` (this branch).

## 2. The "all paths" statement

### 2.1 (a) The mechanical gate: `etc/auth-mediation-check.py`

**It reads:**

1. **The registered methods**, from the Go source at the etcd pin (`.lake/go-src/etcd`, the checkout
   `etc/verified-code.py` already uses):
   - the `Register<X>Server(gs, …)` calls in `v3rpc/grpc.go`'s `Server` and in `embed/serve.go`;
   - each service's descriptor in its `*_grpc.pb.go`: `MethodName:` and `StreamName:` of
     `<X>_ServiceDesc`, with `ServiceName`; health's from the grpc module at `server/go.mod`'s version.

   The result is the list of full names `/<service>/<method>`. A small Go program over `go/ast`
   (`etc/authmed/regs.go`) is sturdier than a regex. It runs with the pinned toolchain, like
   `etc/prophcheck`. It also lists `serveCtx.createMux`'s and `serveClients`' HTTP paths.
2. **The table**, `etc/auth-table.txt`, committed. One line per full name: the class (`public`,
   `authenticated`, `rbac`, `admin`, `mixed`), the status (`e2e`, `e2e-apply`, `contract`, `server`,
   `guard`, `none`, `excluded`), the spec names that carry the row (for example
   `v3rpc.kvServer.Compact.spec`), the guard vocabulary each must mention (`adminWhy`, `authedRes`,
   `permWhy`, `watchAuthed`, `leaseCheckFrom`, `chainClass`/`adminPass`, …), and for
   `excluded`/`none` the issue or note that says why.
3. **The specs**, as their importers see them: `interface/<module>.txt` (CLAUDE.md, "Package APIs":
   the proof file's `wp_proof` with `<F>.spec` unfolded). It also reads `.lake/tcb.json`, when it is
   current, for "linked, no `sorry`".

**It fails when:**

- a registered method has no row. This is the case that matters: a new RPC upstream, or a service
  added to `Server`, fails the gate until someone classifies it;
- a row names a spec that does not exist, or whose unfolded text lacks its guard vocabulary;
- a row's status is stronger than its evidence: `e2e` without a linked `wp_proof`, or with one that
  reaches a `sorry`;
- `--check`: a row's status is weaker than in `etc/auth-mediation-baseline.txt`, or a row is
  missing. `--check --update` only strengthens it, like `bounds-check`.

**Where it runs:**

- `etc/gates.sh`, beside `bounds-check`. The registration and table half needs no build. The
  `tcb.json` half is skipped, with a message, when `.lake/tcb.json` is stale, as `tcb-report`
  refuses.
- CI after the build, for the whole check.

**What it does not do:** decide that a spec's post means "no effect without the check". The
vocabulary test is syntactic. The meaning is reviewed once per row (the spec skill), and the gate
then keeps it from rotting. This is honest about what it is.

### 2.2 (b) The theorem form

Two options were weighed.

- **(b-full) A uniform effect statement over the server's dispatch.** A ghost effect log records
  each apply step, reply, watch registration and lease change with its principal. One invariant
  says every entry's `rowClass` held at a recorded state no older than the request's bound.
  - This is the strongest reading of "no state change or data release without the row's check".
  - It needs a new closed-statement vocabulary (an effect model of every handler) and restates
    every handler's post in it. Most of those posts already say the same in their own terms, so it
    would be a twin of 40-odd specs.
  - Cost: weeks. Not recommended.
- **(b-table) Recommended.**
  1. **Strengthen `v3rpc.Server.spec` in place** (`S/api/v3rpc/Server.lean:47`). Today its post
     says `∀ x ∈ kvRegs q, x ∈ regs` and the like: some registrations are in. The new post says
     the registrations are **exactly**
     `kvRegs q ++ watch ++ leaseRegs ql ++ clusterRegs pc ++ authRegs pa (all 17) ++ healthRegs ++
     maintRegs pm` (as lists, up to the order `RegisterService` keeps). The proof already walks
     every `Register*` call: `descRegs_eq`, `kvRegs_sub` and the like in
     `P/api/v3rpc/InvGrpcStart.lean:100-320`. What is new: the cluster, maintenance and health
     descriptors' lists, and equality where the proof now has inclusion.
  2. **A pure table** `v3rpc.clientPortTable : List (GoString × AuthRow)` in a defs module, from the
     same descriptors as the gate. The gate checks that the table and `etc/auth-table.txt` agree.
  3. **A linking theorem** `client_port_mediated` (`P/api/v3rpc/Mediation.lean`, linking tier):
     - (i) from the strengthened `Server.spec`, every registered full name has a row;
     - (ii) the conjunction, over the rows of status `e2e`/`contract`/`server`, of the handler specs
       the row names, each the existing `<F>.spec` proved by its `Link`. These are not restated;
       they are the same `Prop`s.
     - (iii) the rows of status `excluded` listed with their reason, as a definition the statement
       names, so the exclusions are in the audited statement and not in a comment.

  Lock/Election are not registered by `v3rpc.Server`. They are registered by `embed`, which is
  untranslated. So the theorem is about `v3rpc.Server`'s port, and the gate covers `embed`'s
  registrations as rows of status `excluded`.

**Why (b-table) is honest and checkable.**

- Exhaustiveness is a theorem. The meaning of each row is in a spec that people audit once (the
  `interface/` diff).
- The gate keeps both in step with the Go code.
- Nothing is a twin: the handler specs are strengthened in place where they lack the check (M2-M4),
  and the theorem only conjoins them.
- The SpecPlan's `Server.spec` (`SpecPlan/…/v3rpc/Server.lean:44`, `regsOk B (etcdContract γ ep)`)
  has this exhaustive shape already. This converges toward it, per CLAUDE.md.

**What it does not prove:**

- that a client reaches only these handlers. The client-port listener's other half, the HTTP mux,
  is untranslated. That is a premise of the deployment, named in the statement's docstring;
- anything about the peer port, which is trusted, with peer TLS. The forwarded lease and promote
  calls re-enter there.

## 3. The gaps, with a plan each

### 3.1 Lock/Election (#17502)

**The facts at the pin:**

- The waiting `Watch` of `Lock`, `Campaign` and `Observe` runs on the in-process client's shared
  watch stream, opened with the first waiter's context. Another user's create is checked as that
  user. This is reproduced (`issues/etcd-v3election-shared-watch-wrong-user.md`, rerun 2026-11-14).
- The unary calls (`Unlock`, `Proclaim`, `Resign`, `Leader`, and `Lock`'s and `Campaign`'s `Txn`s)
  go straight to the `kvServer` methods with the caller's context. They run as the caller by
  reading `v3client.New` (`adapter.KvServerToKvClient`), but `v3client` and the adapter are
  untranslated.
- From reading only (to check in M6): the session's keep-alive (`NewSession(WithLease)` →
  `client.KeepAlive`) runs on the in-process lessor's stream, whose context is the client's own,
  with no metadata. With auth on it fails `ErrUserEmpty`. That is fail-closed and harmless: the
  real client keeps its own lease alive.

**Options:**

1. **A named exclusion (recommended now).** The statement covers `v3rpc.Server`'s services. Lock
   and Election are rows of status `excluded`, citing #17502, in the theorem's exclusion list and
   the gate's baseline.
   - The paper says "except the Lock and Election services, where we found that etcd checks a
     waiting call as another user (etcd-io/etcd#17502)". A finding beats a hedge.
   - Cost: none beyond M0/M1.
2. **A premise** ("at most one principal uses Lock/Election at a time"). This is not checkable from
   the code and constrains clients, not etcd. **Not recommended.**
3. **A fixed fork.** The fix: `v3client`'s `watchWrapper.Watch` copies the incoming token into the
   outgoing metadata, so the watcher keys streams per user. Alternatively, open one stream per
   in-process watch. Then translate and prove `v3client.New`, the adapter (`chan_stream.go`, the
   KV/lease/watch adapters) and the client's watcher over a pipe stream.
   - Cost: 3-4 weeks, ~4-6k lines.
   - The maintainers called it a design issue in 2024. A fork fix diverges from what etcd ships
     until upstream takes it.
   - **STOP (fork change, D3).** Recommendation: not now. Revisit if the paper needs Lock/Election.

### 3.2 Streams

- **`RangeStream`** (row 2). Translate `EtcdServer.RangeStream`/`rangeStream`. Prove them over
  `doSerialize`'s spec (the `chk` is the same `IsRangePermitted`), taking `SpecPlan`'s
  `EtcdServer.RangeStream.spec`.
  - The post: every page sent was read after a passing check of `[Key, RangeEnd)` at a state no
    older than `n`. The stated margin is `issues/etcd-rangestream-auth-revoked-midstream.md`: the
    check is not repeated per page, and a revocation mid-stream is noticed only at the end.
  - Then `kvServer.RangeStream`'s spec over it, and the row becomes `e2e`.
  - ~800-1000 lines, 2 sessions (M3).
- **`LeaseKeepAlive`, per renewal** (row 12). The server's `LeaseRenew` states the check on `nil`.
  M0 confirms that `kaStreamSpec` carries `renewAns` to each response; if not, a stronger post in
  place, ~100 lines.
- **`Watch`, per create** (row 7). Done (A4): each created watcher carries `watchAuthed`. There is no
  re-check of live watchers, which is etcd's documented behaviour; the paper says "checked when a
  watch is created".

### 3.3 G4's admin reason (rows 28-42)

`adminTieAr` (`KVAuthModel.lean`) states nothing on a rejected outcome. It is used 21 times in the
waiter's and the request path's exported specs.

- The fix (the guard handoff's): `out = .rejected` ⇒ `adminRefused` at `st`, or the step's own
  error, produced by `adminOut_model` (`ApplyTieOn.lean`) from `adminRejL`.
- It changes exported specs: **STOP**.
- ~300-500 lines, 1-2 sessions (M4).
- It is refusal-completeness, not soundness. The paper line on soundness does not wait for it.

### 3.4 Writes checked only at the API layer; check-to-apply windows

**Who can propose an entry?** Only a member's handler (`raftRequest`), a member's internal job
(lease expiry `WithRoot`, `server.go:881`; the compactor; the cluster-version and member-attribute
publishers; the NOSPACE alarm; downgrade monitoring; lease checkpoints), or a peer (raft, the
trusted port). No client can propose an entry except through a handler. So a write checked only at
the API layer is mediated if every handler proposes only after its check. Each handler's spec says
so: `compactOk`, `alarmTok`, `adminRes`, and `leaseGrantPermitM`'s permit through `reqPropOkM`.

**What is not stated:** the server-level converse, "every applied entry of kind K was proposed after
a check". That is a provenance invariant over the raft log, a ghost permit per proposal. `reqPropOkM`
(`EtcdServer__raftRequest.lean:60`) already threads one for the KV, lease-grant and auth requests;
compaction, alarm, downgrade and membership conf changes do not have it.

- Stage M5 (optional): carry the permit to apply for those kinds, and state at apply that an
  applied entry of an API-checked kind carries a passed check's permit, or was proposed by an
  internal job.
- ~1.5-2k lines, 3-4 sessions. Needed only for a "state change" reading at the state machine. The
  per-handler statement already gives "no handler proposes it without the check".

**The windows between check and apply**, all fail-open for a revocation that races the request.
etcd accepts them; they are recorded:

- membership: `server.go:1403-1408`'s TOCTOU comment;
- `Compact`: `nonissues/etcd-compact-admin-check-lagging-member.md`;
- the lease keys: the TOCTOU issue and the lagging-member nonissues;
- `nonissues/etcd-write-tls-principal-auth-enable.md`.

The specs state these as margins: the check is at a recorded state no older than the caller's bound
`n`, not at the effect. The paper line says "checked when the request is served". No new finding
here.

### 3.5 TLS identities and the gateway

The principal from a client certificate's CN (`AuthInfoFromTLS`) is outside the model: x509 is
axiomatized, D-AU6, and the closed theorems run without TLS.

The gateway reaches the gRPC server over loopback; it is outside the verified code (a security-sensitive finding in the HTTP gateway, recorded privately (etcd-grove-private)).

The statement therefore excludes:

- TLS-CN authentication: "a principal is a token's user";
- the gateway: a row of status `excluded` per HTTP path, in the gate.

Covering the gateway means translating grpc-gateway's `annotateContext` and `embed`. That is
transport work, which the user ranks low ("Transport is low priority"). Not planned.

### 3.6 Other paths checked

- **The interceptors** (`newUnaryInterceptor`, `newStreamInterceptor`: proved) check leadership,
  learner status and capability, not auth. No handler relies on them for auth.
- **The peer port's `/members/promote/<id>`** re-checks admin with the forwarded token
  (`etcdhttp/peer.go:143-149`, #20757's fix). With no token, `IsAdminPermitted(nil)` refuses.
- **The peer port's `/leases` and `/leases/internal`** serve forwarded renewals and TTLs **without**
  an auth check, after the follower's check. Peer port, trusted; recorded in
  `nonissues/etcd-lease-checks-lagging-member.md`.
- **The maintenance server's inner methods** are reached only through `authMaintenanceServer`:
  `NewMaintenanceServer` returns the wrapper.
- **`v3client`'s maintenance adapter** (`NewMaintenanceServer(s, nil)`) is used only by the Lock and
  Election services' client, which never calls it.

No path without a check was found on the gRPC port beyond #17502 (the HTTP gateway is excluded; see §3.5).

## 4. Stages, estimates, risks, STOPs

| stage | what | Lean lines | sessions | builds | STOP |
|---|---|---|---|---|---|
| **M0** | Matrix corrections. `etc/auth-table.txt`, `etc/authmed/regs.go`, `etc/auth-mediation-check.py` with its baseline, in `etc/gates.sh` and CI. Confirm row 12's stream post | 0 (Python ~400, Go ~150) | 1 | none (reads `interface/`) | none (a gate is not trusted text) |
| **M1** | `v3rpc.Server.spec` exhaustive (the cluster, maintenance and health descriptor lists, equality); `clientPortTable`; `client_port_mediated` with the exclusion list | 400-700 | 1-2 | targeted (v3rpc and importers: every closed theorem's start goes through `Server`), then 1 full | **yes**: an exported spec changes, and a new linking statement names definitions (the table, the exclusions) the paper would cite |
| **M2** | The Cluster service: translate `ClusterServer.*` and `EtcdServer.AddMember`/`UpdateMember`/`PromoteMember` (`member.go`, `server.go`). `encoding/json`'s `Marshal` of a `Member` needs a model: a trust-boundary spec here (a JSON encoding of a struct of strings, bools and ids), or the Perennial change it should be | 800-1200 | 2 | targeted ×2 | **yes** if a JSON axiom is added (trust base); record it in `notes/perennial-changes.md` |
| **M3** | `RangeStream` (§3.2) | 800-1000 | 2 | targeted | no (new specs; SpecPlan's statement) |
| **M4** | G4's admin reason (`adminTieAr`) | 300-500 | 1-2 | targeted, 1 full | **yes** (21 exported uses) |
| M5 (optional) | Provenance of API-checked entries at apply (§3.4) | 1500-2000 | 3-4 | 2 full | **yes** (the apply chain's exported posts) |
| M6 (optional) | Lock/Election via a fork fix and `v3client` (§3.1) | 4000-6000 | 6+ | several | **yes** (fork change, upstream PR) |

**To the paper line (M0-M3, with M4 in parallel): about 2.5-3.5 weeks, 5-7 sessions, ~2.5-3.5k Lean
lines.**

**Risks:**

- M1's equality may need `RegisterService`'s model to preserve the order and the duplicates it
  checks. The model already keeps lists with `Nodup` (`grpc.start'`), so this is low.
- M2's JSON is the real cost. The fallback keeps rows 13, 15 and 17 at `guard`, so the paper's
  "every request" would carry "the membership changes' handlers are verified up to their guard".
- Every closed theorem imports `Server`. M1's statement change rebuilds them: about 1 hour of
  build, no proof change expected beyond `Server.wp_proof`.
- The vocabulary test in the gate can pass a spec that mentions its guard without using it in the
  post. The one-time review per row (the spec-reviewer agent, given the 49 rows' unfolded specs)
  covers that.

**How the paper line could read:**

- After M0+M1: "Every gRPC method etcd registers on its client port is classified. A machine-checked
  theorem shows that the server registers exactly these methods. 38 of the 49 have verified
  handlers that act only after the access check etcd's documentation requires, or are public. The
  others are the Lock and Election services, where we found a call checked as another user
  (etcd-io/etcd#17502), and handlers verified up to their check (membership, streamed range)."
- After M2+M3: "…every gRPC request on etcd's client port, except the Lock and Election services
  (etcd-io/etcd#17502), is served only after the access check its RBAC class requires, checked when
  the request is served."

## 5. Decisions (with recommendations)

- **D1 (the user; decided 2026-11-20).** The gateway finding is security-sensitive: it is kept in
  etcd-grove-private, off `lean` and every public branch.
- **D2.** Adopt (b-table) and not (b-full). Recommendation: yes.
- **D3.** Lock/Election as a named exclusion; no fork fix now. Recommendation: yes. Revisit only if
  the paper needs them.
- **D4.** M2's JSON: a local trust-boundary spec now, with a Perennial change proposed beside it.
  Recommendation: yes. The alternative leaves three rows at `guard`.
- **D5.** M5 (provenance) and M4 (admin reason) are optional for the soundness line.
  Recommendation: do M4, which is cheap and already planned; defer M5.
- **D6.** The paper says "gRPC request", and names the HTTP endpoints that are unauthenticated by
  design. Recommendation: yes.

## 6. Evidence index

- Registration: `server/etcdserver/api/v3rpc/grpc.go:84-93`; `server/embed/serve.go:149-150,
  185-188, 245-248, 331-383, 398-423`; `server/embed/etcd.go:759-773, 807-845`.
- Guards: `server/etcdserver/v3_server.go:138-153` (`Range`), `:155-191` (`RangeStream`), `:574-605`
  (`checkLeaseRenew`), `:607-634`, `:751-783`, `:1277-1291` (`requireAuthInfo`);
  `server/etcdserver/server.go:1396-1415` (`checkMembershipOperationPermission`), `:1494-1545`
  (promote forwarding); `server/auth/store.go:1025-1070` (`AuthInfoFromTLS`), `:1072-1100`.
- The gateway: a security-sensitive finding in the HTTP gateway, recorded privately (etcd-grove-private).
- Lean: the paths in §1. `P/api/v3rpc/InvGrpcStart.lean:79-320` (`kvRegs`, `authRegs`,
  `leaseRegs`, the descriptor lemmas). `Proof/google_golang_org/grpc/InvGrpcRun.lean:173`
  (`grpc.start'`).

## 7. Decisions recorded (2026-11-20)

Approved by the user via etcd-grove-03: D2 (b-table, `client_port_mediated`), D3 (Lock/Election excluded by name),
D4 (local JSON trust-boundary spec for the membership handlers, with a Perennial change proposed), D5 (M4 now, M5
deferred), D6 ("every gRPC request", naming the public HTTP endpoints). D1: the gateway finding stays in
etcd-grove-private. Stages M0-M4 queued after the WAL follow-up and (B').

The v3lock issue's front-matter fix (upstream: known, a duplicate of #17502) is held for stage M0 (patch /shared/tmp/coord-03/authmed-issues.patch), so that this Scope lands notes-only.
