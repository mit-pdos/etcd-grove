# Review of `lease-src`'s Draft (c29cf32a15 against 0a1c2ce85b)

Independent spec review, 2026-11-02, judged by `.claude/skills/spec/PRINCIPLES.md` and the examples
`lease-grpc.md` and `lease-keepalive.md`. Read-only: nothing was built. While I was reviewing,
`HEAD` moved to d458fb3027 (Probe). A finding that commit fixes is marked **stale**. Go source:
`/shared/etcd-grove/.lake/go-src/etcd` at 249d76bea7.

## Findings, by severity

### F1 (high, hard rule "Complete"): `LeaseLeases.spec` and `LeaseRenew.spec` cannot be proved over their callees' specs as they stand

The Draft gives the three entry points `lessorRdPool γl ∗ threadTok` and no slot. The Probe says
the other five proofs follow `checkLeaseTimeToLive`'s pattern: borrow, call, give back. Two of
them cannot, because the lessor call they make needs a slot and the token **at the same time**:

- `lease.lessor.Leases.spec` (`Spec/.../lease/lessor__Leases.lean:32-38`) takes `lessorRd lp γl ∗
  threadTok`. The sort calls `Remaining()`, which borrows a slot of each lease's `expiryMu` with
  the token. `EtcdServer.LeaseLeases.wp_proof` calls it with both
  (`Proof/.../etcdserver/EtcdServer__LeaseLeases.lean:66`).
- `lease.lessor.Renew.spec` (`Spec/.../lease/lessor__Renew.lean:55-60`, an axiom) takes `lessorRd
  lp γl ∗ threadTok`. `EtcdServer.LeaseRenew.wp_proof` calls it with both
  (`EtcdServer__LeaseRenew.lean:294`).

Borrowing from the pool uses up the thread token (Perennial `ThreadPool.lean:97`: "a thread that
needs two copies at once ... needs two thread tokens"). So a goroutine holding `pool ∗ threadTok`
ends up with either a slot or the token, never both, and neither callee spec can be applied.
`lessorRdPool`'s docstring (`InvLessor.lean:750`) lists `Leases` as a call the pool serves, so it
promises a use that does not work today.

Go allows the fix. `Leases()` releases `le.mu` before the sort (`server/lease/lessor.go:472-477`).
`Renew` releases it before `l.expired()`, the checkpointer and the write lock
(`lessor.go:396-414`).

**Fix:**
- Restate `lease.lessor.Leases.spec` to take `lessorRdPool γl ∗ threadTok` (or the pool, the pin
  and the token). It is a proved spec: its proof borrows around `RLock`..`RUnlock` and gives the
  slot back before `sort.Sort`.
- Restate `lease.lessor.Renew.spec` the same way. It is a trust-boundary axiom, so this is a
  trusted restatement for Freeze, and the collections that rest on it should be listed
  (`etc/tcb-report.py --roots 'lessor__Renew'`).
- Add both to the Draft's list and to the plan's "What remains for Prove".

`Leases.spec` has only `LeaseLeases` as a caller, and `Renew.spec` only `LeaseRenew`. I found no
other users with `grep`.

### F2 (high at c29, stale at HEAD): `srvAuthLeaseLb_of_reqM` could not be proved in the off or `any` modes

At c29, `Proof/.../etcdserver/LeaseSrc.lean:36` read `isServerReqM E.authOn s E ρ ∗ srvAuthLb s E ⊢
srvAuthLeaseLb s E`.
- **Off:** `srvAuthLb`'s `authStoreLbM .off` is `True` (`StoreLatest.lean`). `isServerReqM
  false`'s fields hold only `isReqAuth v.auth E.RD` (`InvProposer.lean:426-444`,
  `ReqOn.lean:387-408`), which has no `IsAuthEnabled`, `Revision`, `IsAdminPermitted` or
  permission triples. The exact triples are in the read view (`srvReadFieldsAtM`'s
  `apply.isAuthStore`, `ReadOn.lean:67-95`).
- **`any`:** no premise supplies `authApplyErrIs` for `isAuthStore`'s `applyErrIs` errors.

d458fb3027 restated it as `srvAuthLeaseLb_of_server (hM : E.authMode = .off ∨ ∃ γa, E.authMode =
.on γa) : isServerReadM E.authOn s E γr ∗ srvAuthLb s E ⊢ srvAuthLeaseLb s E`. I checked that
version in each mode:
- **Off:** it is provable. `isAuthStore`'s triples (`apply/Contracts.lean:218-235`) give
  `enabledVerdict .off = ⌜b = false⌝`, which is `enabledVerdictFrom .off` (`auth/Fresh.lean:58`).
  `revisionVerdict .off` is `True`, the same as `revisionVerdictFrom .off`. `permCheck2` and
  `permCheck3` already post `authApplyErrIs`, with `permVerdict .off = permVerdictFrom .off`.
  `IsAdminPermitted`'s `M.isOn = false → err = nil` gives `authApplyErrIs` through
  `authApplyErrIs_nil`.
- **On:** it is immediate from `authStoreLbM_lease`, both fields agreeing at `srvAuthStoreAddr`.
- **`hM`:** callers can supply it. `NewServer.specM`/`specG` export `E.authOn = on ∧ (on = true
  → ∃ γa, E.authMode = .on γa)` (`NewServer.lean:440, 626`), and `.off` is the only mode with
  `isOn = false` (`auth/Model.lean:368`).
- **`srvAuthLb`:** it is the right second premise. With auth on, `Start.specOn` exports it
  (`EtcdServer__Start.lean:82`); with auth off, `srvAuthLb_off` derives it (it is `True`).

Nothing left.

### F3 (medium, the bounds rule): the bounds gate fails

`etc/bounds-check.py --check` (run read-only in the worktree, at HEAD) reports:
- `bounds: stock in go_etcd_io/etcd/server/v3/lease: 3, baseline 2`
- `FAILED (391 against the baseline's 390)`

The new match is `lessorRdPool_init`'s `[∗list] _x ∈ List.replicate n (), lessorRdOf`
(`InvLessor.lean:1017`). The plan says "nothing added to the bounds count"; that is false, and
`etc/gates.sh` and CI will refuse the branch.

**Fix:** per `notes/bounds-plan.md`, the stock should become a pool where the lock's owner hands
it out. That owner is the lessor: `NewLessor.spec` gives the `actualMaxReaders` slots, and it is
an axiom (`Proof/.../lease/NewLessor.lean:26`). Either:
- state the pool as a corollary next to it, `NewLessor.spec_pool : NewLessor.spec → …`, giving
  `lessorRdPool γl` plus the two owners' slots, with no new axiom, and have `NewServer` use that;
- or list `InvLessor.lean`'s init lemma in `etc/bounds-allow.txt` as an owner's match, with the
  reason.

The first also keeps the `2^30 - 2` arithmetic out of `NewServer`.

### F4 (medium, "every premise has a source"; target 6, for the served stage): no per-run thread token for a served lease call

Both lease contracts take a thread token per call: `S := E.RD ∗ threadTok` and `S' := E.RD ∗
threadTok ∗ …`. With the pool, every lessor call needs it as well.

Under grpc's runtime, the per-run resource is the `S` of `grpcHandlerOk`
(`Proof/google_golang_org/grpc/InvGrpc.lean:151-157`). Today's run slot, `client.etcdGrpcSlot` /
`etcdRunSlot` (`Proof/go_etcd_io/etcd/client/v3/Results.lean:829-831, 906-907`), holds reader
slots and `E.RD` but no `threadTok`, and nothing in the grpc model hands a handler goroutine its
thread token: there is no `threadTok` anywhere under `Spec/google_golang_org/grpc` or
`Proof/google_golang_org`. The KV handlers never needed one; the `Range`, `Put` and `Txn` specs
take none. `LeaseServer.LeaseKeepAlive`'s proof forks with `HS` (`LeaseServer__LeaseKeepAlive.lean:51`),
so the stream's `S'` needs the token from the run too.

So the registration this commit adds is enough to *find* the lease methods (see target 6), but a
served lease call still has a premise that nothing in the current construction supplies. This gap
predates this commit (the slot-based `S` had `threadTok` too), but the plan's next stage does not
name it.

**Fix:** decide the token's source before the served stage. The natural one is the run goroutine's
own token, since grpc forks one goroutine per stream: a `threadTok` in `grpcHandlerOk`'s
precondition and postcondition, a change to this repository's grpc model. Record the decision in
the plan.

**Uncertain:** whether a variant of the grpc server spec I did not find already handles this.

### F5 (low, "know what it rests on" and docstring accuracy): the restated `leaseTimeToLive` axiom

I believe the restated axiom (`Spec/.../EtcdServer__leaseTimeToLive.lean:52-61`) is true of Go,
including for a goroutine that holds one thread token.
- **Leader path** (`server/etcdserver/v3_server.go:636-675`): `waitAppliedIndex` (channels and a
  timer). Then `s.lessor.Lookup`, which takes `le.mu.RLock` and releases it on return
  (`lessor.go:458-462`); the slot is borrowed for it and given back. Then `le.Remaining()` and
  `le.Demoted()` (each read-locks `expiryMu` and releases it, `lease.go:99-125`), `le.TTL()` (no
  lock) and `le.Keys()` (read-locks `l.mu` and releases it before return). Each runs with the
  token, one after another, and nothing holds two locks at once.
- **Follower path**: `waitLeader` uses `RaftCluster.Member`, which takes `c.Lock()`, a plain mutex
  (`api/membership/cluster.go:134-138`). Then `leasehttp.TimeToLiveHTTP`. Neither touches
  `le.mu`, and the axiom already covered this path before.

Problems:
- The docstring (lines 31-33) says the slot is "given back before `Keys()`, which takes the token".
  `Remaining()` (before `Keys()`) and `Demoted()` (after) take the token too. Name all three.
- The plan says this is "a weaker premise, a stronger axiom". That is imprecise. `pool ∗ tok` and
  `slot ∗ tok` are incomparable: neither entails the other, since a borrow uses up the token. It
  is a different trusted claim, justified by the ordering above.
- Per the "strengthen in place" rule, list the collections that rest on it
  (`etc/tcb-report.py --roots 'leaseTimeToLive'`) for Freeze. A same-name change does not show up
  in `--check`.

### F6 (low, "no unneeded premise"): `checkLeaseLeases.spec` takes the pool and uses nothing of it

Go's `checkLeaseLeases` (`v3_server.go:751-785`) makes no lessor call: it walks the given leases'
`Keys()`, which borrow from each lease's pool with the token (`keysPre .reader`,
`InvLessor.lean:846`). The old slot was only framed through
(`EtcdServer__checkLeaseLeases.lean:39-269`, `Hrdo` never consumed). The restatement keeps the
unneeded premise in pool form at `Spec/.../EtcdServer__checkLeaseLeases.lean:40`.

**Fix:** drop `lease.lessorRdPool γl` from the pre. `srvLessorRd s γl` looks unneeded there as
well (pre-existing; check the proof).

### F7 (low, target 6): two small gaps in the descriptor facts

- **Nodup no longer stated:** `svcDescsOk`'s Lease clause (`BaseStart.lean:117-124` at c29)
  replaces `descOk`, which carried `(descNames mds sds).Nodup`, with the exact lists, and drops
  Nodup. `RegisterLeaseServer.spec` asks for `⌜(descNames mds sds).Nodup⌝`. It follows from the
  exact lists, but there is no `v3rpc.leaseDesc_nodup` beside `kvDesc_nodup`, `authDesc_nodup`
  and `watchDesc_nodup` (`InvGrpcStart.lean:125, 178, 252`), and the Probe's list does not
  mention it. Add it.
- **The Lease stream stated twice:** `etcdserverpbDescs` (`cache/v3/Base.lean`) now has the new
  exact clause and the older `ClientStreams' = [true]` clause, each with its own `∃ ssl sds` over
  the same field. Merge them into one clause, as the Watch clause does: `sds.map (·.ClientStreams')
  = [true]`.

### F8 (low, process): a `sorry` inside a proved construction

`authStoreKit_on`'s `sorry` (`AuthSrv.lean:356-363` at c29) puts a `sorry` under every auth-on
result that goes through the kit, until Prove. This is fine on a Draft branch, but it must not
merge, and the TCB baseline must not be `--update`d with it.

### F9 (low, "Local"): `NewServer`'s post gains a stage-specific conjunct again

`NewServer.spec`, `specM` and `specG`'s posts each gain `lease.lessorRdPool E.γ.leases`
(`NewServer.lean:294, 482, 668`). It is persistent and cheap to carry, and K7 set the precedent,
but it is the accretion the "Local" rule warns of. If F3's corollary is adopted, the pool comes
with the lessor (`NewLessor.spec_pool`). It could then travel with whatever already carries the
lessor's facts to the discharge, though `srvLessorRd` itself stays the server's view, as the plan
argues. Worth putting to the user; not required.

## By target

### 1. `lessorRdPool`, its lemmas, and the seven specs

**Good:**
- The definition is minimal and persistent.
- The two lemmas match Perennial's `threadPool.init` and `borrow`/`giveBack` exactly
  (`ThreadPool.lean:76-140`).
- Borrowing per lessor call fits what Go does: every call releases `le.mu` before touching a
  lease's lock.
- `checkLeaseTimeToLive` and `checkLeaseRenew` follow it exactly: `Lookup`, then `Keys()`
  (`v3_server.go:596-603, 625-632`).
- The posts rightly lose the slot.

**Findings:** F1 (`LeaseLeases`, `LeaseRenew`), F3, F5, F6.

### 2. The discharges and their restatements

**Good:** the pool is a persistent premise of the theorem, not of the per-call `S`, which shrinks
to `E.RD ∗ threadTok`. The handlers' contracts at any `S` are unchanged, so the frozen handler
specs stay put.

**Issue:** the restatements are only as good as F1. `raftLeaseRead_of_server`'s
`LeaseLeases` branch and `raftLeaseRenew_of_server` rest on the two specs that cannot be proved
today. The docstring "no premise but the server's facts and the bounds"
(`ServerLeaseRead.lean:39-41`) should now name the pool.

### 3. `NewServer`'s last conjunct

**True and suppliable:**
- `NewLessor` gives `actualMaxReaders` slots.
- `NewServer`'s proof takes two and drops the rest (`Proof/.../NewServer.lean:634-635`), which
  leaves `2^30 - 2`.
- `lessorRdPool_init` needs `threadBound GF ≤ 2^30 - 1`, and `NewServer` has `≤ 2^28`.
- The pool is on `E.γ.leases`, the same name as `srvLessorRd`'s.

**Findings:** F3 and F9 (where it should come from).

### 4. `IsAdminPermitted.specLb` and `auth.adminVerdictFrom`

**Good:**
- The shape matches the other `specLb`s: the reader's `authRd`, `a ↦{dq} info`, `authPubLbM M n`
  and `authErrIs`.
- It is provable from the named callees:
  - With `IsAuthEnabled.specLb` reading `false`, `adminOk`'s first disjunct holds at that state,
    which is no older than `n` (`auth/Model.lean:205-207`).
  - Otherwise `lockedReadTx.specLb`'s state (also no older than `n`) has the user with the root
    role, the second disjunct. `adminOk` does not need that state's `enabled`, so the TOCTOU
    between the two reads is harmless.
  - Errors get the flag read's state as their witness.
  - `authRd` splits into `enabledRd ∗ cacheRd ∗ beRd ∗ R` (`InvAuth.lean:1861`), which covers
    both callees' pres.

**Strong enough for `isAuthStoreLeaseLb`:** yes. The clause posts `authApplyErrIs`, which follows
from `authErrIs` (`apply/AuthDerive.lean:131`). The rest of the clause is the specLb's post, with
`isPkgInit`, `authInv` and `authPubLbM` persistent in `isAuthStoreLeaseLb_of_authInv`'s context.

**The `nil` omission is right.** All three checks return `ErrUserEmpty` on `authInfo == nil`
before calling `IsAdminPermitted` (`v3_server.go:584-586, 616-618, 765-767`). Go's own nil and
empty-user branch (`store.go:919-921`) is covered: the `""` username gives an error, and the
verdict says nothing on errors.

**Margin:** the docstring states that no refusal is described. A third proved spec of the function
(`spec`, `specL`, `specLb`) follows the E3h/E3j precedent of the permission checks.

### 5. Moved definitions, `authStoreLbM`, the source

**Good:**
- The move keeps the frozen text unchanged: `leaseCheckFrom` and `leaseCheckT` still say
  `adminVerdictFrom`, now delegating.
- `authStoreLbM`'s mode-on body is strengthened in place, not as a mode-indexed copy.
- The `rfl` unfolds in `Range`, `Txn` and `ReadOn` are replaced by projection laws
  (`authStoreLbM_range`, `authStoreLbM_lease`), which is good law coverage.

**Findings:** F2 (stale at HEAD; the restated version is provable in `.off` and `.on`, and `.any`
is excluded by `hM`, which callers can supply), F8.

### 6. The Lease registration

**Good:**
- `leaseDescMethods` and the stream list match `rpc_grpc.pb.go:695-725` exactly: four methods in
  order with their handlers, and `LeaseKeepAlive`.
- `leaseRegs` and `leaseSReg` use the full names `/etcdserverpb.Lease/<M>` over the
  `*quotaLeaseServer`, as `kvRegs` does.
- `ServerMethodSets` already has `lease_impl`/`lease_te`.
- `NewQuotaLeaseServer.spec`'s post is exactly the two new persistent facts.
- The `lcid lmid` ids are existential and separate from the KV's, as the lease-grpc review
  requires (`fill` overwrites them).

**Enough for the served stage?** Compared with `etcdKVRegs` and `etcdGrpcSlot`, the post gives
what a served call needs from `v3rpc.Server`: the registration entries, the service objects, and
`leaseServerAt … C.A`, whose `revR` is the contract's `R`. Three things are left:
- the two names-only generated handlers (acknowledged in the plan);
- `leaseDesc_nodup` (F7);
- a per-run `threadTok` (F4).

## Ranking by need of revision

1. **The seven specs**, because of `LeaseLeases.spec` and `LeaseRenew.spec` (F1). This needs
   restated `lessor.Leases.spec` and `lessor.Renew.spec`; the latter is an axiom, for Freeze.
   Also F6.
2. **The pool's placement and the bounds gate** (F3, which affects targets 1 and 3).
3. **Target 6** (F4 for the next stage, F7).
4. **The `leaseTimeToLive` axiom** (F5: docstring and the list of collections; the statement
   itself looks sound).
5. **Target 5** (F2 stale; F8 is process only).
6. **Target 4** (no finding).

No bug in the Go code was found, so nothing goes in `issues/`.
