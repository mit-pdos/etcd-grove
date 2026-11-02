# The lease discharges' sources and the Lease service's registration (2026-11-02)

Spec-first, as `notes/lease-keepalive-plan.md`. Branch `lease-src`. After the lessor/auth list
(items 1-6 done), the first of the gaps they left (`notes/STATUS.md`, the keep-alive stream's
"Gaps"): no proof supplies the lease discharges' premises, and no served client can reach the
lease handlers.

## Scope (2026-11-02; the user's choices)

**What is missing.** `raftLeaseRead_server` and `raftLeaseRenew_server` (`v3rpc/Results.lean`)
discharge the handlers' contracts from the linked entry points, over:
- `srvAuthLeaseLb s E` (`LeaseCheck.lean`): the auth store's `IsAuthEnabled`, `Revision`,
  `IsAdminPermitted`, `IsPutPermitted`, `IsRangePermitted` with their verdicts no older than any
  lower bound of the published index. **No source.** `IsAdminPermitted` has no lower-bound spec.
- per call, `lessorRdOf γl` (a reader slot of the lessor's lock). `NewLessor` gives `2^30`, and
  `NewServer` keeps two (the store's and the apply thread's lease owners) and **drops the rest**.
- `srvLessorRd`, `srvPeerRt`, `srvHeaderFacts`: given since the keep-alive stage.

And `v3rpc.Server.spec` registers the KV, Watch and Auth services but **not the Lease service**:
its proof calls `NewQuotaLeaseServer` and `RegisterLeaseServer` and drops what they give.

**The user's choices (2026-11-02):**
- **"Sources + registration"**: both sources, and `v3rpc.Server.spec` restated to give the Lease
  service's registrations (`TimeToLive`, `Leases`, the `KeepAlive` stream) over the
  `*quotaLeaseServer`/`*LeaseServer` objects, as `kvRegs` does. A client example calling a lease
  read through a served server is the next stage.
- **"Both modes"**: `srvAuthLeaseLb` with auth off (from the store's exact triples) and with auth
  on (the store's invariant; a new `IsAdminPermitted.specLb` in the auth package, over the existing
  `lockedReadTx.specLb`).
- **"Thread pool"**: the lessor's remaining reader slots in a Perennial thread pool
  (`threadPool.init`), borrowed with the caller's thread token, as `lgMu`'s (J8a), following
  `notes/bounds-plan.md`; nothing added to the bounds count.

## The design

**The pool.** `lease.lessorRdPool γl` (persistent): `∃ γp, threadPool.isThreadPool N γp (lessorRdOf
γl)`. `NewServer`'s proof makes it from `NewLessor`'s slots less the two it keeps (`2^30 - 2 ≥
threadBound GF` since `threadBound GF ≤ 2^28`). No axiom changes: `NewLessor.spec` already gives the
`2^30` slots.

**Who borrows.** A request's goroutine has one thread token, and the lease checks already need it:
`Keys()` borrows a slot of the lease's own lock with it. So the slot can't be borrowed for the whole
call. The checks borrow it around each lessor call instead (`Lookup`, `Leases`): borrow (the token
for a slot), call, give back (the slot for the token), then `Keys()` with the token. The checks'
specs and the three entry points' specs take `lessorRdPool γl` (persistent) in place of
`lessorRdOf γl` (owned), and the discharges' per-call `S` loses `lessorRdOf γl`:
- `EtcdServer.checkLeaseTimeToLive.spec`, `checkLeaseRenew.spec`, `checkLeaseLeases.spec`;
- `EtcdServer.LeaseTimeToLive.spec`, `LeaseLeases.spec`, `LeaseRenew.spec`;
- `raftLeaseRead_of_server`, `raftLeaseRenew_of_server` and their `Results.lean` restatements.

`EtcdServer.leaseTimeToLive.spec` (the trust-boundary contract approved in item 2, an **axiom**) takes
`lessorRdOf γl ∗ threadTok` too: `LeaseTimeToLive` cannot borrow around it, since the contract needs
the token as well. So it takes the pool in place of the slot (a weaker premise, a stronger axiom:
true of Go, whose leader path calls `Lookup` and then `Keys()`, one after the other). **A trusted
statement**, for the user at Freeze.

The handler specs (`LeaseServer.*`) are over a contract at any `S` and do not change. **These are
frozen statements** (the lease-read, lease-renew and lease-grpc stages'): the restatement is for the
user's review at Freeze, with a `notes/decisions.md` entry.

Alternative rejected: `srvLessorRd` absorbing the pool (one fewer premise), because `srvLessorRd` is
the server's view of its lessor field, and the pool is the lease package's.

**`srvAuthLeaseLb`'s source.**
- *Auth off*: from `isServerReq`'s `isAuthStore … .off` (the exact triples): `enabledVerdictFrom
  .off` is `b = false`, `adminVerdictFrom .off` is `err = nil` (`isAuthStore`'s `M.isOn = false →
  err = nil`), the permission checks the same. A lemma `srvAuthLeaseLb_off`, as `srvAuthLb_off`.
- *Auth on*: as `authStoreLbM` (E3s) comes from `IsRangePermitted.specLb` in `EtcdServer.start`
  (`srvUberBase`), an `authStoreLeaseLbM` from the five `specLb`s, in `srvUberBase` beside it, and
  `srvAuthLeaseLb_of_uberBase`. New: `auth.authStore.IsAdminPermitted.specLb` and its proof.
  `srvUberBase` is internal to the server (not a frozen spec); `EtcdServer.start`'s proof builds it.

**The registration.** `v3rpc.Server.spec`'s post gains `∀ x ∈ v3rpc.leaseRegs ql, x ∈ regs`,
`v3rpc.leaseKASReg ql ∈ sregs`, `quotaLeaseServerAt ql ⟨…LeaseServer…, #pl⟩ s ∗ leaseServerAt pl
s …` (what `NewQuotaLeaseServer` gives). A frozen spec too (the server start's item 4), the same
kind of change as the KV's and Auth's registrations.

## Draft (2026-11-02)

- `lease/InvLessor.lean`: `lessorPoolN`, `lessorRdPool γl`, `lessorRdPool_init` (`n` slots,
  `threadBound GF ≤ n + 1`), `lessorRdPool_borrow` (`pool ∗ threadTok ⊢ |={E}=> ▷ lessorRdOf γl ∗
  (lessorRdOf γl ={E}=∗ threadTok)`).
- The seven specs (`checkLease{TimeToLive,Renew,Leases}`, `Lease{TimeToLive,Leases,Renew}`, the
  axiom `leaseTimeToLive`): `lessorRdPool γl` in the pre in place of `lessorRdOf γl`, which leaves
  the post. The discharges (`ServerLeaseRead.lean`, `Results.lean`): `lessorRdPool γl` a premise, `S :=
  E.RD ∗ threadTok`, `S' := E.RD ∗ threadTok ∗ srvLgReader s ∗ srvReadReader s γr`.
- `NewServer.spec`/`specM`/`specG`: the posts end with `lease.lessorRdPool E.γ.leases`.
- `auth/FreshAdmin.lean` (new): `auth.adminVerdictFrom` (the body of `LeaseCheck.lean`'s, moved to the
  auth package) and `auth.authStore.IsAdminPermitted.specLb` (a non-nil `authInfo`; the passing
  verdict at a state no older than `n`), `wp_lb` over `IsAuthEnabled.specLb`, `lockedReadTx.specLb`,
  `hasRootRole.spec`.
- `etcdserver/AuthLeaseLb.lean` (new): `adminVerdictFrom` (now `auth.adminVerdictFrom`),
  `permCheck2Lb`, `isAuthStoreLeaseLb` moved from `LeaseCheck.lean` (unchanged otherwise), and
  `isAuthStoreLeaseLb_of_authInv` (from the five `specLb`s).
- `StoreLatest.lean`: `authStoreLbM`'s mode-on body gains `isAuthStoreLeaseLb st RD (.on γa) n`.
  `srvAuthLb` (which `Start.specOn` exports) carries it, so no spec of `Start` changes.
- `etcdserver/LeaseSrc.lean` (new): `srvAuthLeaseLb_of_reqM : isServerReqM E.authOn s E ρ ∗ srvAuthLb s
  E ⊢ srvAuthLeaseLb s E`.
- The registration: `etcdserverpbDescs` (`cache/v3/Base.lean`) and `svcDescsOk` (`BaseStart.lean`)
  state the Lease descriptor's methods and stream exactly (`v3rpc.leaseDescMethods`, the
  generated literal of `rpc_grpc.pb.go:695-725`), as the Auth service's (E3zb); `InvGrpcStart.lean`:
  `v3rpc.leaseRegs ql` (the four methods), `v3rpc.leaseSReg ql` (`LeaseKeepAlive`), with
  `leaseRegs_sub`, `leaseSReg_mem`; `v3rpc.Server.spec`'s post: `ql pl lcid lmid`, both
  registrations, `quotaLeaseServerAt ql … s ∗ leaseServerAt pl s C.A lcid lmid` (both persistent).
- Left to the served stage: the generated `_Lease_LeaseTimeToLive_Handler` and
  `_Lease_LeaseLeases_Handler` are names only (`etcdserverpb.toml` translates Grant, Revoke and
  KeepAlive's), so a served client cannot run them yet.

## Stages

Draft → Review (an independent spec reviewer) → Test → Probe (the hard proof: one check's borrow
and give-back around `Lookup`; the easy one: `srvAuthLeaseLb_off`) → Freeze (the user) → Prove.
