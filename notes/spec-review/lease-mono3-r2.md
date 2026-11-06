# Spec review: lease-mono3, round 2

Reviewer: independent subagent, 2026-11-06. Branch `lease-mm` at `00edf6d0f3` (worktree
`/shared/etcd-grove-leaseexp`), against round 1 (`notes/spec-review/lease-mono3-r1.md`, on
`2a4632ab5c`) and the fix log (`notes/lease-mono3-plan.md`, "Review round 1 fixes (2026-11-06)").
Judged by `.claude/skills/spec/PRINCIPLES.md`. I changed nothing in the repository apart from this
file. The only build command was `lake build --packages=/shared/tmp/manifest-84d.json --no-build` on
`leasecatchup.Results`, `partition.Results`, `putget3.Results`, `k8s.compactor.Results` and
`restart.Run`. It reported "All targets up-to-date (7843 jobs)" and replayed the `#print axioms`
output, in which `sorryAx` does not appear.

**No BLOCKER.** Every round-1 fix resolves its finding, and I found no new false statement. What
is left: one process item (round 1's trust-base finding, still open by decision), one landing item
(new: `lean` moved), and NITs.

## 1. The fixes, finding by finding

| r1 finding | fix | verdict |
|---|---|---|
| §2 SF: no `.mono` elimination law; `run` unfolded six definitions | `cluster3.memberAt_mono` (`Defs.lean:366-379`); `run.lean:99-100` uses it | **Resolved.** `run` no longer unfolds `memberAt`, `servedRegs`, `etcdLeaseServedAt` or `etcdLeaseGrantAt`. The law is stated at the literal `.mono`, as "a law over a free mode" asks. It is stated from the consumer's goal (registrations at the bridge `b`, `isGrpcRpc_forwards` folded in), and it is true: its proof is the projection of `memberAt`'s conjuncts. What it moves rather than removes is a NIT, N1 below. |
| §2 SF: `servedRegs` an inline copy of `etcdKVAt` with a `rest` continuation | `servedRegs m c s E ρ cid mid` (`Defs.lean:173-177`): `.none => etcdstart.etcdKVAt c E ρ ρ.rd cid mid`; otherwise `etcdLeaseReadAt c ∗ etcdLeaseServedAt m …` | **Resolved.** The `.none` arm is the old inline text. `etcdKVAt` (`Served.lean:46-52`) at `γr := ρ.rd` gives the same five registrations: Range at `ρ.rd`, Txn at `ρ.rd ρ.rd`. `memberServed_none` and `memberAt_none` keep their statement text (diff of `00edf6d0f3`: only the proof term changed) and are now proved by `simp only [… etcdKVAt, sep_assoc_eq]` (`:234, :355`). That is a law, not `rfl`, as "A new mode redefines … in place (laws, not `rfl`)" asks. `servedRegs_sep`/`_join` are gone (`StartCluster.lean`), following "drop what existed only for what it changed". |
| §2 SF: `servedRegs_persistent` unfolded `etcdLeaseServedAt` | `etcdstart.etcdLeaseServedAt_persistent` (`ServedLease.lean:102-105`, in `interface/…/ServedLease.txt`) | **Resolved.** `servedRegs_persistent` (`Defs.lean:179-181`) is now `cases m <;> unfold servedRegs <;> infer_instance`. |
| §5 SF: pure premises as implications in the new leasecatchup specs | `run.spec` (`Spec/…/leasecatchup/run.lean:59-68`), `Main.spec`, `grant.spec`, `leases.spec`: `⌜…⌝` conjuncts of the precondition | **Resolved.** `Adequacy.lean:173-177` discharges them with `ipureintro` from the same hypotheses it passed before. `Main.lean` and `run.lean` introduce them with `%H` in `wp_start`. |
| §1 SF (process): the `.none` closed results gained `leaseTimeToLive.wp_proof`, `sort.Sort.wp_anyLess` | not changed; baselines committed in `e9ec46b4b1`; the plan's "Left" says putting it before the user at Freeze "stays open" | **Still open, by decision.** The committed `linkv3p.txt` and `k8scompactor.txt` (+2 each) make `--check` consistent at `HEAD`. The user's explicit acknowledgement is still owed (P1 below). |
| §1 NIT: stale "granting no lease" / "KV and watch" | `Spec/…/StartMember.lean:11-12, 56`, `StartCluster.lean:13-15` | **Resolved.** The new wording is true in every mode. |
| §1 NIT: frozen specs keep implications | left, with the reason in the plan | **Acceptable.** The principle says "convert one when you change it", and these triples did change (`StartMember.lean:68`, `StartCluster.lean:65`). Converting three of about twenty would mix the styles in one triple, and the plan defers the conversion to the next statement change. Leave it, but convert at the next change. |
| §2 NIT: `clusterAt`'s pure conjunct twice | `(match m with \| .none => etcdKV … \| _ => True) ∗ ⌜…⌝` (`Defs.lean:401-405`) | **Resolved.** `clusterAt_none` is still `rfl` (`:424`). |
| §2 (a) the doubled `LeaseLeases`; §2 (b) the TTL read | left, with the reason | **Acceptable.** Both are persistent and harmless, and the reasons in the plan's "Left" are accurate. |
| §3 NIT: `alloc3`'s defaults unusable | `lm hrun hrev` before `(cmp := false) (cret := 0)` (`interface/…/Alloc3.txt:65-66`) | **Resolved.** putget3 (`Main.lean:243`) and restart (`Run.lean:237`) no longer pass `false 0`, and StartCluster passes `cmp 0` explicitly. |
| §3 NIT: `if decide` gate | left | Acceptable (consistent with `alloc1`). |
| §5 NIT: the `leasesNoExpiry` paraphrase | `Spec/…/run.lean:22-24`, `Adequacy.lean:18-20` | **Resolved.** Both now quote `LessorBackend.lean:50-57`: "no lease of any lessor the program creates (… granted there, or reloaded by `Recover`) expires … while the program runs". |
| §5 NIT: stale tcb header | `etc/tcb-collections/leasecatchup.txt:9-10` | **Resolved.** |

## 2. Does the cluster3 vocabulary and leasecatchup still say what the Go does?

**Good.**
- `cluster3.go` has no lease mode: the mode is ghost-only. Go's `StartMember` (`cluster3.go:102`)
  serves all of `v3rpc.Server(s, …)` in every mode. `memberServed`/`memberAt` at `.mono` register
  the lease reads, `LeaseGrant`/`LeaseLeases` at the member's lessor history, the watch stream and
  `noRefusalAt`. They drop the KV calls, a deliberate margin documented in the `Defs.lean` header
  (`:22-27`: "the KV calls make no claim in a cluster that grants leases"). The margin is weaker
  than Go, never stronger, so it is sound.
- `memberAt_mono` is per member, at `E.γ.leases` of that member's server. This matches the
  member-local listing (`v3_server.go:737-749`, `ServedLease.lean` header). A cluster-level
  contract would be false.
- The leasecatchup specs match `leasecatchup.go`:
  - `grant` (`:118-123`) and `leases` (`:126-131`) are a timeout context, one call and `cancel`.
    Each post is the reply's `ID` (resp. the `Leases` slice) with the caller's `Q`, or an error.
  - `run.spec`'s header states the Go steps: start, two clients, `g1` through member 3, two cuts,
    20 filler attempts, two mends, bounded polls. Its post, "returns some `int`", does not panic.
    The proof shows the panic branch dead: `run.lean:257-269` hands `[g1]` with its grant to the
    listing, and `rw [decide_eq_true Hin]` at the second `listed`.
  - Not promising `Checked` is the right margin: catching up is liveness, which the spec cannot
    promise.

**Remaining remarks (NIT).**
- N2, below: `clusterAt`'s docstring is stale at a granting mode.

## 3. Is `etcd_leasecatchup_safe` still meaningful, every premise discharged?

**Yes.**
- `Results.lean:62-94` is unchanged by `00edf6d0f3`. It restates `etcd_leasecatchup_adequate`,
  whose hypotheses are those of round 1.
- In `Adequacy.lean:173-177`, every conjunct of `Main.spec`'s new pure precondition is discharged
  from a hypothesis or a fact:
  - `Hbf`;
  - the bounds, from `HT`/`HN` by `omega`;
  - the write budget, by unfolding the constants;
  - `Hck … Hdbo`, `Hlp`, `Hlne`;
  - `ServerMethodSets` by `inferInstance`;
  - `AsTarget` by `rpctypesEtcdError_asTarget`.
- The replayed `#print axioms` output has no `sorryAx`. `leaseTimeToLive.wp_proof` and
  `MustUnsafeGetAllLeases.wp_proof` are among the axioms, as round 1 noted.
- The claim is closed (fresh state, one thread, every `n`-step real execution) and no-panic for
  every thread.
- Round 1's uncertainty stands, inherited and not new. `Hlne` is read over the model's executions
  after `Main` returns too (`LessorBackend.lean:59-62`). I did not verify that no model execution
  sends on `expiredC`, so this remains **uncertain**.

## 4. Did the callers' statements stay unchanged?

**Yes.**
- `git diff lean...HEAD -- Spec/` touches only `leasecatchup/*`, `cluster3/StartCluster.lean`,
  `StartMember.lean` (docstrings and the round-1-reviewed premises) and `holdToken.lean`.
- For putget3, partition, restart and the k8s compactor, the diff touches proofs only:
  - partition `Main.lean`, `MainWatch.lean`, `startCluster.lean`;
  - compactor `MainPartition.lean`;
  - putget3 `Main.lean`;
  - restart `Run.lean`.
- The changed lines pass `.none`, `lease.runCfg_none`, `(by decide)` and `(fun h => absurd rfl h)`,
  replace `iunfold memberAt` with `isimp only [memberAt_none]`, and recover the `alloc3` gate.
- No `Results.lean` or `Adequacy*.lean` of those callers changed, and `memberAt_none`'s text is
  unchanged (§1).
- The one change of meaning is the trust base (P1).

## Findings

### SHOULD-FIX

- **P1 (process; trust boundary, carried over from r1 §1).** `etcd_partition_safe` (linkv3p) and
  the k8s compactor's results rest on `EtcdServer.leaseTimeToLive.wp_proof` and
  `sort.Sort.wp_anyLess`, which they did not rest on at `lean`.
  - Source: `linkv3p.txt:21, 574` and `k8scompactor.txt:17, 615` (the diff `71c9d0ee60..HEAD`).
  - Affected: every `.none` caller of `StartMember`.
  - The decision is recorded as H1 (A) under etcd-grove-82's delegation, and the plan leaves it open.
  - Restatement: at Freeze, show the user the two axioms and the closed results that gained them,
    with the alternative named. That alternative is `memberServed` without `etcdLeaseReadAt`, so
    no TTL row and no `leasePeersOk` in leasecatchup, which never calls `TimeToLive`.
- **P2 (landing; new since r1: `lean` moved).** Since the merge base `71c9d0ee60`, `lean` added
  `rpctypes.ErrGRPCCompacted_init` and `ErrGRPCFutureRev_init` (7c-1b's HS-1, `fd22898429`) to
  every server collection: leasekv, leaseexpiry, linkv3p, k8scompactor, putget3, ….
  - `etc/tcb-collections/leasecatchup.txt` exists only on this branch, and its rpctypes block
    (`:63-72`) lacks both. leasecatchup reaches the same package initializers as leasekv, so after
    merging `lean`, `tcb-report.py --collection …/leasecatchup.txt --check` would likely fail in
    `etc/land.sh`'s gates.
  - I did not merge or run it, so this is **uncertain**.
  - `linkv3p.txt`/`k8scompactor.txt` change in different hunks on the two sides, so the merge
    should apply cleanly.
  - Restatement: merge `lean`, then rerun `--check --update` on leasecatchup and confirm the
    delta is exactly those two lines.

### NIT

- **N1 (a client does not unfold another module's definitions).** `memberAt_mono` (`Defs.lean:375`)
  unfolds `etcdstart.etcdLeaseServedAt` and `etcdstart.etcdLeaseGrantAt`, and `memberServed_none`/
  `memberAt_none` (`:234, :355`) unfold `etcdstart.etcdKVAt`.
  - All three are in etcdstart's API module `ServedLease`/`Served`. So SF2 moved the unfold from
    leasecatchup into cluster3 rather than removing it.
  - leasegrant (`Main.lean:157, 170`), leaseexpiry (`Main.lean:189`) and txnlin/k8s etcd3 already
    do the same, so this is pre-existing debt of etcdstart's API, not new to this round.
  - Restatement: next to the definitions in `ServedLease.lean`, add the following, and let
    `memberAt_mono` and leasegrant/leaseexpiry use them:
    - `etcdLeaseServedAt_none … = etcdKVAt …` and `etcdLeaseServedAt_mono … = etcdLeaseGrantAt
      addr E` (`rfl`, at the literals);
    - an elimination `etcdLeaseGrantAt addr E ⊢ isGrpcRpc addr LeaseGrant … ∗ isGrpcRpc addr
      LeaseLeases …`.
- **N2 (stale docstring).** `clusterAt`'s docstring (`Defs.lean:385`) still lists "the client's
  view of etcd's KV at the start store" unconditionally. At a granting mode the arm is `True`
  (`:403`). Restatement: "in the mode `none`, the client's view of etcd's KV at the start store".
- **N3 (caller burden; pre-existing pattern).** `run.lean:93-97` still unfolds `clusterUp` and
  `clusterAt` and destructures them positionally. The plan says this is what every cluster3
  client does (partition `startCluster.lean:64`, `Main.lean:84`), and that is true.
  - Under "every unfold is a missing law", this is the next law for cluster3: an elimination of
    `clusterUp` giving the three `memberAt`s, the `srvPeerCtl`s and the bridges.
  - It is not this round's to fix.
- **N4 (grouping).** `run.spec` puts `lg ≠ null` inside `⌜BootFacts … ∧ lg ≠ null⌝`
  (`Spec/…/run.lean:63`). Those are unrelated facts. A separate `⌜lg ≠ null⌝` reads better and
  matches `StartCluster`'s premise order.

## Ranking by need of revision

1. **Trust base and landing (process)**: P1 (the user's acknowledgement of the two axioms at
   Freeze) and P2 (leasecatchup's baseline after merging `lean`). Neither is a spec defect.
2. **`cluster3/Defs.lean`**: N1 (laws belong in etcdstart), N2 (stale `clusterAt` docstring) and
   N3 (`clusterUp` elimination, pre-existing).
3. **leasecatchup specs**: N4 only. The fixes are correct and the closed theorem holds.
4. **`StartMember`/`StartCluster`, `Alloc3`, `ServedLease`**: no revision needed this round.
5. **Callers** (putget3, partition, restart, k8s compactor): statements unchanged; no revision.
