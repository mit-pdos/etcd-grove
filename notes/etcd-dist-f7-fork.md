# F7 option "(fork)": `LeaseTimeToLive` re-checks the keys it returns (2026-11-26, SPECULATIVE)

Branch `etcd-safe-f7-fork/2026-11-26` off `etcd-safe-f7-rlog` @ `c5b8bb0348`. **Speculative**: pending
Upamanyu's decision on the F7 options (`notes/etcd-dist-f7.md`, Handoff S5-3; `notes/etcd-dist-f7-bprime.md`
on branch `etcd-safe-f7-bprime`). Nothing here lands, and nothing here is decided.

The plan (the lead's brief): (1) fix etcd on the fork so that `LeaseTimeToLive` checks read permission on
the keys it returns; (2) re-translate at the new revision; (3) re-prove `EtcdServer.LeaseTimeToLive.wp_proof`,
its post strengthened (every returned key readable by the principal); (4) add the reply-keys claim to
`Lease_TimeToLiveOn_dist`; (5) (b') in the dist `foreign`, link `RunAuthLease`, `etcd_safe_nocrash` loses
`HauthLease`; (6) build, gates.

**Status: step 1 done, step 2 checked (not committed), step 3 STOPPED** at the brief's stop condition: the
new body cannot be proved without changing a second trusted statement, the contract (axiom)
`EtcdServer.leaseTimeToLive.wp_proof`. The exact text is below, for the lead and Upamanyu.

## Step 1: the Go fix (done)

Fork checkout `/shared/etcd-fork-ttlkeys` (a worktree of `/shared/etcd`), branch `goose-lean-ttlkeys`, commit
**`d26dd5da6f383bc9b06a957d685360dc12f8faf2`** on the pin `df6af0c36a` (branch `goose-lean`). Local only, not
pushed (Upamanyu pushes the fork).

- `server/etcdserver/v3_server.go`: `LeaseTimeToLive`, with `r.Keys`, after `leaseTimeToLive` returns (the
  leader's own lookup or the forwarded reply) and **before** the auth-revision re-check, calls a new
  `checkLeaseTimeToLiveKeys(ctx, resp.Keys)`: auth disabled → ok; `AuthInfoFromCtx` (error, or nil →
  `ErrUserEmpty`); admin → ok; else `IsRangePermitted(authInfo, key, []byte{})` on each returned key, the first
  error returned (`ErrPermissionDenied` for an unreadable key; `ErrAuthOldRevision` if the token's revision is
  stale, as in `checkLeaseTimeToLive`). The same shape as `checkLeaseTimeToLive`; refusing, not filtering (the
  current semantics: one unreadable key fails the request). The key check precedes the revision re-check, so
  when the re-check passes every check ran at the check's auth revision.
- `tests/integration/v3_lease_test.go`: `TestV3LeaseTimeToLiveKeysPermission` (leader / follower), the
  regression test, the issue's reproduction asserting `rpctypes.ErrPermissionDenied` (gofail failpoints
  `beforeLookupWhenLeaseTimeToLive`, `beforeLookupWhenForwardLeaseTimeToLive`, as
  `TestV3LeaseTimeToLiveWithLeaderChanged`).

Runs (go1.27.x, `/shared/tmp/f7fork-gotest/{fixed,base}`, copies of the fork at `d26dd5da6` and at the pin with
the same tests, `gofail enable server/etcdserver/ server/lease/leasehttp/`, plus the test-only failpoint
`applyAfterRecoverLessor`, `failpoint.patch`):

| test | pin `df6af0c36a` | fork `d26dd5da6` |
|---|---|---|
| `TestV3LeaseTimeToLiveKeysPermission/leader` | FAIL (reply not refused) | PASS |
| `TestV3LeaseTimeToLiveKeysPermission/follower` | FAIL | PASS |
| `TestF7forkLeaseKeysAfterSnapshot` (bprime's `TestF7bLeaseKeysAfterSnapshot`, ported) | FAIL: 143 replies passed, each disclosing `z/lease` | PASS: 0 passed, 572 refused |
| `TestV3LeaseTimeToLiveWithLeaderChanged`, `TestV3LeaseTimeToLiveStress`, `-run 'Auth.*Lease\|Lease.*Auth'` | PASS | PASS |

The port (`f7fork_lease_keys_snapshot_test.go` here) calls TimeToLive with keys at the follower through the
whole snapshot window (12 s, the apply sleeping 3 s between `lessor.Recover` and `kv.Restore`) and asserts that
no reply discloses `z/lease` (bprime's asserted the first unrefused reply did not). With the fix every call was
refused: the forwarded reply carries `z/lease`, which the re-check refuses. So (b') ("refused, or the reply
discloses no key the user may not read") holds in Go at the fork.

## Step 2: the re-translation (checked, not committed)

`etc/goose.py --project etcd --src etcd=/shared/etcd-fork-ttlkeys --perennial /shared/perennial-a706aeb9a`
(the pinned Perennial) changes only `Code/go_etcd_io/etcd/server/v3/etcdserver.lean` (`LeaseTimeToLive.impl`'s
new call and the new `checkLeaseTimeToLiveKeys.impl`; the rest are `go:` line numbers), once
`EtcdServer.checkLeaseTimeToLiveKeys` is added to `Code/go_etcd_io/etcd/server/v3/etcdserver.toml`
(`etcdserver-toml.patch` here: without it goose emits the call but no method, and `GeneratedProof` is
unchanged either way). Diff: `Code/.../etcdserver.lean | 196 +++++----`, `etcdserver.toml | 3 +`; full patch
kept at `/shared/tmp/f7fork-translation.patch`. Not committed: without step 3 it would leave
`EtcdServer.LeaseTimeToLive.wp_proof` unbuildable, and the pin bump (`etc/goose.py`'s `rev`, `examples/go.mod`
and the `examples/k8s/*/go.mod` replaces with their sums) needs the fork commit pushed for `--check`.

## Step 3: STOPPED: the new body needs the `leaseTimeToLive` contract to give the reply's keys

`checkLeaseTimeToLiveKeys` reads `resp.Keys[i]` and passes each to `IsRangePermitted`, whose spec
(`Spec/.../auth/authStore__IsRangePermitted.lean`) takes `key ↦*{dk} k ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝`. The
response comes from `leaseTimeToLive`, names-only, whose spec is the trust-base contract `axiom
EtcdServer.leaseTimeToLive.wp_proof` (`etc/tcb-baseline.txt`); its success arm owns `resp ↦ w` and the header,
nothing of `w.Keys'` (the slice of key slices, and each key's bytes). No other fact in scope gives them. So
`LeaseTimeToLive.wp_proof` over the new body needs the contract's post to own the keys: a change to a trusted
statement beyond the two the brief allows (the dist TimeToLive axiom's reply-keys claim, and
`EtcdServer.LeaseTimeToLive.spec`'s strengthening, which is proved, not trusted).

**The change it needs** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`,
`EtcdServer.leaseTimeToLive.spec`'s success arm). Before:

```lean
      ((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗
          ⌜w.Header' ≠ null⌝ ∗ ⌜w.ID' = v.ID'⌝ ∗ (∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∗
          □ (leaseTTLRow s γl -∗
```

After (one conjunct, ownership only; nothing about which keys):

```lean
      ((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗
          ⌜w.Header' ≠ null⌝ ∗ ⌜w.ID' = v.ID'⌝ ∗ (∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∗
          (∃ kbs : List GoSlice, w.Keys' ↦* kbs ∗
            [∗list] kb ∈ kbs, ∃ k : List w8, kb ↦* k ∗ ⌜sint.Z kb.len < 2 ^ 63 - 1⌝) ∗
          □ (leaseTTLRow s γl -∗
```

Why it would be true of Go (to be confirmed by an `axiom` review before use): on the leader
(`v3_server.go:637-670`) `resp` is a fresh literal; with `r.Keys` its `Keys` is `kbs := make([][]byte,
len(ks))` with each `kbs[i] = []byte(ks[i])` (fresh copies of the lessor's key strings), without it `nil`
(`nil ↦* []`); on a follower the reply is decoded by `leasehttp.TimeToLiveHTTP` (`http.go:224-278`) from the
leader's HTTP body into a fresh `LeaseInternalResponse`, whose `[]byte` fields the protobuf decoder copies out
of the body buffer (to check: protobuf-go's default `Unmarshal` does not alias the input; the buffer is not
retained), and nothing else holds the returned message. The length bound: a key is at most etcd's request
size, far below `2^63 - 1` (a stated fact, as the contract states its other facts).

**What step 3 would then be** (not started): a spec and proof for `EtcdServer.checkLeaseTimeToLiveKeys`
(post on `nil`: `leaseCheckFrom (srvTLSId s) E tok n (fun info => [∗list] k ∈ ks, auth.permVerdictFrom
E.authMode n info k [] .read GoInterface.nil)`, `ks` the keys' bytes; the loop as
`checkLeaseTimeToLive.wp_proof`'s, l.175-230), and `EtcdServer.LeaseTimeToLive.spec`'s success arm gaining,
with `v.Keys'`, the keys' ownership and that second `leaseCheckFrom` over them (a separate existential
principal: the helper calls `AuthInfoFromCtx` again; both are bound to `tok` by `principalBound`). Ledger
entry first (`notes/specs-only/ledger.md`). Callers (`ServerLeaseRead`'s `raftLeaseRead_of_server`, the
`ServedLease*` of `etcd_authlease`, the v3rpc handler) keep their proofs: a stronger post.

## Step 4 (drafted only): the dist axiom's reply-keys claim

`Lease_TimeToLiveOn_dist`'s success arm would gain, with keys asked, informally: `∀ k ∈ r.Keys,
permVerdictFrom (Γ.au mid) n info k [] .read nil` for the principal `info` bound to the caller's token, at an
auth state no older than the member's floor `n` (the member's applied auth state, as reads' `authFloorD`; a
grant revoked at the leader but not yet applied at the member still passes). The exact Lean text waits for
step 3's server-side form, so that the dist-axiom-diff pair matches.

## Left, once the contract change is decided

1. The fork: Upamanyu pushes `goose-lean-ttlkeys` (`d26dd5da6`).
2. Step 2: apply `etcdserver-toml.patch`, re-translate, bump `etc/goose.py`'s etcd `rev` and the
   `examples/go.mod`, `examples/k8s/{dist,compactor,etcd3,all}/go.mod` replaces (pseudo-version
   `v3.0.0-<commit time UTC>-d26dd5da6f38`, sums from `go mod tidy`), `etc/goose.py --check`.
3. The contract change above (ledger entry, `axiom` review, tcb baseline unchanged in names), then steps 3-6 of
   the plan. Build host: fk-lean2 has 18 GB free of 484 GB and the base tree (`~/eg/wt/etcd-safe-f7-rlog`) is
   63 GB, so the brief's `cp -a` copy does not fit; space must be freed (or that tree reused) first.

## Session K (2026-11-26): steps a-d of the approved plan

The lead and the coordinator approved, speculatively and on this branch only, two trusted text changes, each with
a fresh delta review (`axiom` skill).

- **a. Translation** (`c5f0a53378`): `etcdserver-toml.patch` applied; `etc/goose.py --project etcd --src
  etcd=/shared/etcd-fork-ttlkeys` (only `Code/.../etcdserver.lean` changes; no other project translates etcd at
  this pin: `RaftNoAx`/`KvRaft`'s walpb parts are the same run). `etc/goose.py`'s etcd `rev` is `d26dd5da6f38…`;
  the `examples/go.mod` and `examples/k8s/{all,compactor,dist,etcd3}` replaces are
  `v3.0.0-20261126150644-d26dd5da6f38` with sums computed from the local fork (`go mod download` with
  `GOPROXY=direct` and a git `insteadOf` to `/shared/etcd`; the sums are content hashes, so they are what the pushed
  commit will give); `etc/featuregate-allow.txt`'s module paths bumped likewise. **`etc/goose.py --check` cannot
  verify an unpushed revision by itself**: it passes with `--src etcd=/shared/etcd-fork-ttlkeys` (and the fork's
  modules in the Go module cache, as above); CI's plain `--check` fails until the fork commit is pushed.
- **The avoid route** (none): no proved callee gives the reply's key bytes: `leaseTimeToLive` is names-only (a
  contract) and the follower's decode, `leasehttp.TimeToLiveHTTP`, is names-only too (only `RenewHTTP` of
  `leasehttp` is proved), so the bytes `IsRangePermitted` needs can only come from the contract's post.
- **The `Unmarshal` aliasing**: protobuf-go v1.36.12 (etcd's `go.mod`) has no generated `Unmarshal` for etcd's
  messages (protobuf-go v2, `protoimpl`); a repeated `bytes` field decodes through `consumeBytesSlice`
  (`internal/impl/codec_gen.go:5568-5580`): `*sp = append(*sp, append(emptyBuf[:], v...))`, a copy, with no
  `AliasBuffer` case. Test: `notes/etcd-dist-f7-fork/unmarshal_alias_test.go` (`TestF7forkUnmarshalKeysNoAlias`,
  the follower's decode exactly; overwriting the body leaves the keys, writing the keys leaves the body): PASS.
- **b. Ledger** (`notes/specs-only/ledger.md`, 2026-11-26) and **change 1** (`EtcdServer__leaseTimeToLive.lean`):
  the success arm gains `(∃ kbs : List GoSlice, w.Keys' ↦* kbs ∗ [∗list] kb ∈ kbs, ∃ k : List w8, kb ↦* k ∗
  ⌜sint.Z kb.len < 2 ^ 63 - 1⌝)`.
- **c.** `EtcdServer.checkLeaseTimeToLiveKeys` spec and proof (new; linked in `etc/link-lean-first-server.txt`),
  `EtcdServer.LeaseTimeToLive.wp_proof` re-proved over the new body; its spec's success arm gains, with `v.Keys'`,
  `∃ kbs ks, w.Keys' ↦* kbs ∗ ([∗list] kb;k ∈ kbs;ks, kb ↦* k) ∗ leaseCheckFrom (srvTLSId s) E tok n (fun info =>
  [∗list] k ∈ ks, auth.permVerdictFrom E.authMode n info k [] .read GoInterface.nil)`. Callers: only
  `ServerLeaseRead.raftLeaseRead_of_server` changed (it drops the new conjunct before `ttlAns`). Lean-checked on
  fk-lean2; server `Link.lean` regenerated (487d74f4ae).
- **d. Change 2** (`LeaseTimeToLiveOnDist.lean`): the success arm gains, with keys,
  `∃ ks kbs kss, Keys resp ↦□ ks ∗ ks ↦*□ kbs ∗ ([∗list] kb;k ∈ kbs;kss, kb ↦*□ k) ∗ leaseCheckD (Γ.au mid)
  (principalOf cfg) n (fun info => [∗list] k ∈ kss, auth.permVerdictFrom (.on (Γ.au mid)) n info k [] .read
  GoInterface.nil)` (`n` the member's published auth index `≥ n₀`, as the existing keys verdict); dist-axiom-diff's
  dev lines rewritten (ok). axiom-tok keys: to check after the full build (`axiom-tok-check.py --check`).

### Handoff K-2 (2026-11-26; steps a-d done, e half started, f-g not started; context limit)

Branch `etcd-safe-f7-fork/2026-11-26`, worktree `/shared/etcd-grove-f7fork`. No `sorry`, no axiom added; the
only trusted text changes are the two approved ones (change 1 `EtcdServer.leaseTimeToLive.spec`, change 2
`Lease_TimeToLiveOn_dist.spec`, both above).

- **Build host** fk-lean2, tree `~/eg/wt/etcd-safe-f7-rlog` (content `c5b8bb0348` plus this branch's diff):
  `/shared/tmp/f7fork-rb.sh [targets]` syncs `git diff --no-renames c5b8bb0348` (+ untracked, deletions) and runs
  `lake build` under flock/MemoryMax=55G (log `~/eg/logs/f7fork-build.log`); `CHECK=1 … -a -q FILE` runs
  `etc/lean-check.py`; `/shared/tmp/f7fork-chk.sh FILES` checks files in turn; `/shared/tmp/f7fork-gl.sh MODE
  OUTFILE` runs gen-link there and copies the file back. Lean-checked green on fk-lean2: `checkLeaseTimeToLiveKeys`,
  `LeaseTimeToLive`, `ServerLeaseRead`, dist `noAuth`, dist `foreign` (the last two only their `icases` patterns:
  `Hck, -⟩`, the new conjunct dropped). A build of `etcdserver.Link` + `v3rpc.Results` was started at handoff (no
  result recorded here: rerun it).
- **e. Reviews**: review 1 (change 1) was launched as a subagent writing
  `notes/axiom-review/f7fork-leasettl-keys-contract.md` (+ `f7fork-leasettl-keys-gotest/`); if that file is absent
  or unfinished, rerun it (the brief: delta = the new conjunct; settle the follower's decode aliasing in code and
  by a test). Review 2 (change 2, `notes/axiom-review/f7fork-ttl-dist-keys.md`, cited in the axiom's docstring)
  NOT started: after review 1, one subagent with the `axiom` skill; the delta is the `if leaseKeysFold gs false
  then ∃ ks kbs kss, …` conjunct; evidence the fork's `checkLeaseTimeToLiveKeys` and the in-process
  `EtcdServer.LeaseTimeToLive.spec` keys conjunct; points to probe: the client's `Keys` field aliasing the `pb`
  response (`lease.go:257`), grpc's decode buffer pooling (protobuf copies), the index `n` (member-local auth
  state, a revoked-at-leader grant passes), the admin arm.
- **f. Not started.** Plan: (1) Go: `examples/etcd/dist/client/authlease.go` `foreign`: TimeToLive with keys
  panics only if it succeeds AND a returned key is one the user may not read (the forbidden key passed in: `zK` for
  u/`Lz`, `aK` for v/`Lu`, as `RunAuthLease` calls it); Leases: keep the call, no panic (its reply carries no key,
  and at a member applying a snapshot its refusal is false, `notes/etcd-dist-f7-bprime.md`); retranslate
  (`etc/goose.py --project putget-dist`, check which project owns `examples/etcd/dist/client`), `go test
  ./etcd/dist/`. (2) Spec `Spec/.../dist/client/foreign.lean`: the TimeToLive refutation premise becomes one over
  the forbidden key: `□ (∀ n info-free…, leaseCheckD (Γ.au mid) (principalOf cfg) n (fun info => permVerdictFrom
  (.on (Γ.au mid)) n info k [] .read nil) -∗ R ={⊤}=∗ False)` for `n ≥ n₀`; the Leases premise and `m₀`/`Γ.ls`
  injectivity go. (3) `foreignReads.law` (`ForeignReadsLaw.lean`) is then replaced by a PROVED lemma from the frozen
  auth floor (`authFloorD_frozen`, `leaseCheckD_none_frozen`-style: u may not read `z/`, v may not read `a/` at
  `setupSt r`), no lessor law needed; `RunAuthLease.lean` passes it instead of `hlaw`. (4) Link `RunAuthLease`
  (Handoff S5-7 "Left"; nothing to port from `etcd-safe-f7-bprime` @ `6e76f1ae90` but its Go test, which narrowed
  to option (b) instead) and close `EtcdAuthLeaseBootNC` as `EtcdAuthBootNC` was (Handoff W-6 items 2-6 / B-1 for
  kind 6: the auth-on start at the revocable mode for `[authLease]`, `wlShare` kind 6, `MainReady`'s kind-6 arm,
  assembly); `etcd_safe_nocrash` drops `HauthLease`, its statement and `etcd_robust_nocrash.spec` otherwise
  byte-identical.
- **g. Not started**: full build, `etc/gates.sh` in full (with `LAKE_OPTS=--packages=.lake/package-overrides.json`
  on fk-lean2), `axiom-tok-check.py --check` (the two changed axioms' keys), `tcb-report --check` (names
  unchanged expected; `foreignReads.law` is a hypothesis, not an axiom), then push.
- **Review 1 done** (after K-2): `notes/axiom-review/f7fork-leasettl-keys-contract.md`, SOUND (tests in
  `f7fork-leasettl-keys-gotest/`, all pass: no key aliases the body, even with `UnmarshalAliasBuffer`); its one nit
  (a docstring line range, 268 → 269) applied. Rows in `notes/axiom-review/README.md`/`notes/audit.md` not added
  yet. Next: review 2.

### Handoff K-3 (2026-11-26; e done, f stopped at a missing fact, g not started)

- **e done.** Review 2 (`notes/axiom-review/f7fork-ttl-dist-keys.md`, Go test `f7fork-ttl-dist-keys-gotest/`):
  **SOUND** (the client's `Keys` is the decoded reply's, `lease.go:246-261`, retries reset it; grpc v1.84.0 frees
  its receive buffer after `Unmarshal` but protobuf-go v1.36.12 copies every repeated `bytes` element; the verdict
  is member-local at states of index `≥ n`; admin/auth-off arms claim nothing per key; lease-not-found answers
  no keys). Its docstring nit applied (`61d32a2122`); index rows for both reviews in `notes/axiom-review/README.md`
  (`notes/audit.md` rows not added).
- **f(1) done** (uncommitted at the time of writing, then committed with this handoff): `foreign(cli, who, id,
  forbidden)` in `examples/etcd/dist/client/authlease.go`: TimeToLive with keys panics only if it succeeds and a
  returned key is `forbidden` (`zKey` for u/`Lz`, `aKey` for v/`Lu`); `Leases` called, its result ignored
  (`_, _ =`). Retranslated (`etc/goose.py --project putget-dist --src etcd=/shared/etcd-fork-ttlkeys`: only
  `Code/.../dist/client.lean`). `go test ./etcd/dist/`: PASS; a real deployment `DIST_RUN=1 DIST_WANT=authLease
  go test -short -run 'TestDist$'` (3 members, auth on): `authLease: checked`, PASS. **The Lean build breaks at
  `foreign` until f(2)** (its spec still names the 3-argument function).
- **f(2)-(4) NOT done: a fact the plan assumed is missing.** `Lease_TimeToLiveOn_dist.spec` (and
  `Lease_LeasesOn_dist.spec`) take `lease.lessorLb (Γ.ls mid) m₀` in their precondition (trusted text, unchanged),
  so `foreign`'s spec must keep `m₀`, `lessorLb (Γ.ls mid) m₀` and `Γ.ls`'s injectivity (the plan's "the Leases
  premise and `m₀`/`Γ.ls` injectivity go" is wrong for the precondition; only the Leases *refutation* premise goes).
  `RunAuthLease` has a `lessorLb` only at `a0` and `au` (`lease.leaseLiveFrom_lb` of root's and u's `grantPut`,
  l.449-450); **v's `foreign` runs at `av = eps[2 mod k]`, a third member when `k ≥ 3`, where no fact of the
  client machine gives `lessorLb (Γ.ls midv) _`**: until now `foreignReads.law` (a hypothesis) supplied it.
  `lessorSlot` publishes only `lessorHistOk` and a pin (no lower bound), `barrierFloor` only `authFloorD`. Options
  (a decision for the lead):
  1. Go: v's client at `au` (`newUserClient(au, "v", vPw)`): `midv = midu`, `Hlbu` serves; loses v's check at a
     third member.
  2. Publish a lower bound in the slot: `lessorSlot`'s right disjunct gains `lessorLb γl 0` (the member's
     `NewLessor` has it), plus a client lemma "a served member's slot is closed" (from `etcdAddrAt`/`Serve_dist`
     facts: not found; may need the start's facts in `RunAuthLease`'s precondition). Definitions and the member
     proofs change; no trusted text.
  3. v (or root) grants a lease at `av` first (Go change; the authLease cell `γc.ids` is `[Lz, Lu]`, so the cell
     model would change).
  The rest of f(2)-(4) is as planned: the refutation premise over the forbidden key `k`,
  `□ (∀ n, ⌜n₀ ≤ n⌝ -∗ leaseCheckD (Γ.au mid) (principalOf cfg) n (fun info => auth.permVerdictFrom (.on (Γ.au mid))
  n info k [] .read GoInterface.nil) -∗ R ={⊤}=∗ False)`; its proof in `foreign` walks the returned keys (the
  `[∗list]` of `kss`, `big_sepL2` lookup at the equal key, `leaseCheckD` mapped to that key's verdict); the lemma
  replacing `foreignReads.law`: `n₀ := m` (the floor's `authPubLbM`), `authFloorD_frozen` for `st = setupSt r`,
  arms refuted by `leaseCheckD_none_frozen`'s pattern (auth enabled), `etcd_authlease.not_adminOk_setupSt` (admin)
  and `etcd_authlease.not_permitted_setupSt` (with `not_inRangeK_zK` for u; v reads nothing), all existing.
- **Build** (step 1 of this session, fk-lean2, at `059eaf26f0`'s content): `etcdserver.Link` + `v3rpc.Results`: success (10439 jobs). The earlier failure in `AuthSrv` was read-only `.ilean` files, not a proof error.
- **g not started.**

### Handoff K-4 (2026-11-26; option (2) stopped before any Lean edit: the client lemma needs trusted text)

The lead chose option (2): `lessorSlot`'s right disjunct publishes `lessorLb γl 0`, plus a lemma "a served member
has made its lessor" giving `RunAuthLease` the `lease.lessorLb (Γ.ls midv) m₀` at `av`, with no `Spec/`, axiom or
`TopLevelRobustness` text change. **Stopped (the brief's stop condition): the lemma has no premise to come from.**

- Publishing `lessorLb γl 0` in the slot is easy (`newLessor_alloc_at` closes the slot holding the reader invariant;
  `lessorLb_get` + `lessorLb_le`). But a client reads the right disjunct only if it can refute the left one,
  `ghostMapAuth γl ½ ∅`, and that needs a fragment of `γl`'s map (`lessorPinR`, inside every `lessorAt`/`lessorLb`):
  the very fact sought.
- What the client holds of v's member `midv` at `foreign`'s call: `leaseMember Γ av` (made by the start before any
  machine runs: `etcdAddrAt` + `lessorSlot`, `Start.lean`'s `leaseMembers_of`), the barrier's `KV_GetOn_dist` post
  (`authFloorD`: `authPubLbM`/`authStateAt` of `Γ.au midv`, log bounds) and v's `New` client. No lease call reaches
  `av` before `foreign` (`barrier` is a `Get`; `newUserClient` is `clientv3.New`). None of these names `Γ.ls midv`
  or a ghost name tied to it.
- A defs-only tie (a start invariant "`Γ.au mid`'s history grew ⇒ `lessorLb (Γ.ls mid) 0`") needs a share of the
  member's auth authorities, which `NewServer_dist`'s premise `authNamesFreshD γa` takes whole (trusted text);
  `memberUpOnL` (which has `srvLeaseRd` and `mvccLeases E.γ = γl`, so a member-side `memberUpOnL ⊢ |={⊤}=> lessorLb
  γl 0` is provable) is consumed by `Serve_dist` (axiom), which publishes nothing.
- Ways out, each outside the brief: (a) a trusted-text change: `KV_GetOn_dist`'s post (or `authFloorD`) carries
  `lessorLb (Γ.ls mid) 0`, or `Lease_TimeToLiveOn_dist`/`Lease_LeasesOn_dist` drop `lessorLb` from their
  precondition (their posts already return `lessorLb (Γ.ls mid) j`); (b) option 1 (v's client at `au`) or option 3
  (a grant at `av` first: `LeaseGrant`'s post gives `lessorLb` there), Go changes with no trusted-text change.
- Nothing else changed: `ab2cec0a79`'s tree, plus this entry. f(2)-(4), g not started; the Lean build still breaks at
  `foreign` (its spec names the 3-argument function).
