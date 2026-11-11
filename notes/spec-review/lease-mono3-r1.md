# Spec review: lease-mono3, round 1

Reviewer: independent subagent, 2026-11-06. Branch `lease-mm` at `2a4632ab5c` (worktree
`/shared/etcd-grove-leaseexp`), against `lean...lease-mm`. Context: `notes/lease-mono3-plan.md`
"Scope" §1–§8 only. Judged by `.claude/skills/spec/PRINCIPLES.md`. I did not modify the repository
apart from this file. The only build command was `lake build --no-build` on
`leasecatchup.Results`, which reported everything up to date and replayed the `#print axioms`
output.

**No BLOCKER.** The closed theorem has no `sorry`. `etcd_leasecatchup_safe`,
`etcd_leasecatchup_adequate` and `leasecatchup_Main` print 3153, 3153 and 2046 axioms, none of
them `sorryAx`. The panic is ruled out by the listing spec, not assumed (target 5).

The uncommitted baselines in the worktree add no axiom beyond the union of
linkv3p/leasekv/leaseexpiry/k8scompactor. These are `etc/tcb-collections/{leasecatchup,linkv3p,
k8scompactor}.txt`, modified but not committed.

## 1. `cluster3.StartMember` / `StartCluster` / `holdToken` (frozen)

**Good.**
- `StartMember.spec` is one triple for every mode. It needs no `lm ≠ .revocable`: its proof splits
  on `lm = .none` and uses `kv_lease_served_watch` for every other mode
  (`Proof/.../cluster3/StartMember.lean:205ff`). So the revocable scope premise sits only where
  `alloc3` needs it, at `StartCluster`.
- The premise `(lm ≠ .none → leasePeersOk)` (`Spec/.../StartMember.lean:67`,
  `StartCluster.lean:64`) is needed. `kv_lease_served(_watch)` takes `hP : leasePeersOk` because
  `raftLeaseRead_server` takes it (`ServedLease.lean:210`), and only those modes reach that path.
  The gate keeps every `.none` closed theorem free of the premise.
- `lease.runCfg lm lm` is the subsystem's slot (`LeaseRun.lean:77`). With `lm ≠ .revocable` it
  amounts to `mono → leasesNoExpiry`, which is the premise the server's expiry arm actually needs.
- `lm ≠ .revocable` is necessary. `srvMemberBoot_alloc`'s `hpfx : γk.lm = .revocable →
  γk.ids.pfx = idPfxOf id` (`NewServerAlloc.lean:346`) cannot hold for three members with distinct
  prefixes (`pfx_ne`). It is marked as a scope premise in the docstring, and the plan's §7 files it
  (the related Go finding is `issues/etcd-lease-id-mask-member-prefix.md`, with a failing test).
- `holdToken` follows leasegrant's precedent.
  - `wp_fork_tok_self` is a proved Perennial lemma
    (`/shared/perennial-84d538063/Perennial/GooseLang/Lifting.lean:2006`).
  - A child whose post is `False` never returns its token, so the parent keeping one mints nothing.
  - `holdToken.spec`'s `False` post is sound for an infinite `time.Sleep` loop.
- Every caller discharges the new premises trivially at `.none`:
  `lease.runCfg_none (by decide) (fun h => absurd rfl h)` (partition `startCluster.lean:54`,
  `k8s/compactor/MainPartition.lean:136`).

**Findings.**

- **SHOULD-FIX (process; trust boundary, "check whether collections gain an axiom … put it to the
  user").** The `.none` callers' closed results now rest on two lease-branch axioms:
  `EtcdServer.leaseTimeToLive.wp_proof` and `sort.Sort.wp_anyLess`.
  - These are `etcd_partition_safe` (linkv3p) and the k8s compactor's results.
  - The cause: `StartMember`'s one linked proof takes the callees of every branch.
  - `notes/decisions.md` (the new holdToken entry, "The callers at `none` rest on the lease branch's
    axioms") records it as H1 (A), "decided by etcd-grove-82 under the user's delegation".
  - The baseline updates (`linkv3p.txt`, `k8scompactor.txt`, +2 lines each) are uncommitted in the
    worktree, so at `HEAD` `tcb-report.py --check` on those collections would fail.
  - Two approved closed results gained axioms, and the plan's §4 said "statement text unchanged"
    for the callers. I recommend putting this before the user explicitly at Freeze rather than
    relying on the delegation.
  - The plan's rejected alternative (no `etcdLeaseReadAt` in `memberServed`) would avoid both the
    axiom and `leasePeersOk` for leasecatchup, which never calls `TimeToLive`. It is the margin
    worth naming in the docstring.
- **NIT.** `Spec/.../cluster3/StartMember.lean:55`: the comment "the members' workload, granting
  no lease" is now false (the member may grant leases).
  - `:11` says "etcd's KV and watch services at its client address", and `StartCluster.lean:13-14`
    says "with its KV and watch registrations … and etcd's KV at the start store". Both hold only at
    `.none`.
  - The lease paragraphs added below them correct this, but the triple's summary is what a reader
    reads first.
- **NIT (pure premises in the precondition).** The three new premises are Lean implications.
  - The principle says to convert when a spec changes.
  - For a frozen statement with about 20 existing implications this is a judgment call. Converting
    only the new three would mix the two styles, so leaving it is defensible; say so.

## 2. Vocabulary in `cluster3/Defs.lean`

**Good.**
- `memberServed`, `memberAt`, `clusterAt` and `clusterUp` take `(m := .none)`, and each has a
  `_none` theorem stating its old text (`Defs.lean:216, 338, 391, 420`).
- The `.none` callers moved from `iunfold memberAt` to `isimp only [memberAt_none]` (partition
  `Main.lean:88`, `MainWatch.lean:189`, `MainPartition.lean:152`), which is a law, not an unfold.
- At a granting mode there is no client `etcdKV` (`clusterAt`'s `match`, `Defs.lean:383`). This
  matches `srvClusterBoot_alloc`, and `memberServed` drops the KV registrations whose atomic
  updates no client could supply.

**Does `memberServed … .mono` give what a client needs, and nothing it shouldn't?** It gives:
- the lease reads (`etcdLeaseReadAt`: TTL, `Leases` at `…SpecAny`);
- `Grant` and `Leases` at the member's lessor history (`etcdLeaseGrantAt`, `ServedLease.lean:62`);
- the watch stream, `noRefusalAt`, `srvGoRes`, `srvPeerCtl`;
- the server views, as before.

That is what leasecatchup uses, and it is per member, as the listing's Go semantics requires
(`v3_server.go:737`, the `ServedLease.lean` header's S5).

Two surpluses:
- (a) `LeaseLeases` is registered twice. `…SpecAny` is derivable from `etcdLeaseLeasesSpec
  E.γ.leases` (`isGrpcRpc_leaseLeases_any`, used at `ServedLease.lean:283`) (NIT).
- (b) The TTL read is registered although a multi-member TTL row does not exist. It holds only
  through `leasePeersOk` and the trusted `leaseTimeToLive`, and it is the source of finding 1's
  axiom (see above).

**Findings.**

- **SHOULD-FIX (a client does not unfold; every unfold is a missing law).** The first client at
  `.mono` (`Proof/.../leasecatchup/run.lean:90-99`) unfolds six definitions to reach the grant and
  listing registrations: `clusterUp`, `clusterAt`, `memberAt`, `servedRegs`,
  `etcdstart.etcdLeaseServedAt` and `etcdstart.etcdLeaseGrantAt`.
  - The `.none` mode got `_none` laws; `.mono` got none.
  - Restatement: export `memberAt_lease` (for `m ≠ .none`):
    `memberAt … m ⊢ forwards b c ∗ client.etcdLeaseReadAt c ∗ etcdstart.etcdLeaseServedAt m c s E ρ
    ρ.rd cid mid ∗ …`.
  - Better, a law giving the bridge's registration directly (it folds in `isGrpcRpc_forwards`,
    `run.lean:100-112`): `memberAt … .mono ⊢ isGrpcRpc b LeaseGrant (etcdLeaseGrantSpec E.γ.leases)
    ∗ isGrpcRpc b LeaseLeases (etcdLeaseLeasesSpec E.γ.leases)`.
- **SHOULD-FIX (vocabulary; "a new mode redefines in place … laws, not `rfl`").**
  `servedRegs` (`Defs.lean:171-183`) is an inline copy of `etcdstart.etcdKVAt` (`Served.lean:46`,
  which is `etcdLeaseServedAt .none`) in its `.none` arm.
  - It takes a continuation `rest : IProp` only so that the old text comes back by `rfl`.
  - The `_none` statements are theorems anyway, so the `rfl` constraint is self-imposed. It costs a
    helper whose shape (a predicate parameter threaded through the arms) no reader expects.
  - Restatement: `memberServed`/`memberAt` hold `etcdstart.etcdLeaseServedAt m c s E ρ ρ.rd cid mid
    ∗ (if m = .none then emp else client.etcdLeaseReadAt c) ∗ <rest inline>`.
  - The `_none` laws would then be proved by `etcdKVAt`'s unfolding and associativity in this file
    (the one place allowed to unfold it), or the `_none` laws could be stated over `etcdKVAt`
    directly.
- **SHOULD-FIX (law coverage).** `servedRegs_persistent` (`Defs.lean:188`) unfolds another
  module's `etcdstart.etcdLeaseServedAt`, which has no `Persistent` instance. The siblings
  `etcdLeaseGrantAt_persistent` and `etcdLeaseGrantLiveAt_persistent` have one
  (`ServedLease.lean:68,86`). Add `etcdLeaseServedAt_persistent` next to its definition
  (`ServedLease.lean:95`).
- **NIT.** `clusterAt`'s `match` (`Defs.lean:383-388`) repeats the pure conjunct
  `⌜kvSame … ∧ … cret = 0⌝` in both arms. `(match m with | .none => etcdKV … | _ => True) ∗ ⌜…⌝`
  still reduces to the old text at `.none` by iota, and states the gate once.

## 3. `etcdstart/Alloc3.lean` (hub)

**Good.**
- `alloc3`/`alloc3Http`/`memberBoot_of` take `lm`, `hrun : lease.runCfg lm lm` and
  `hrev : lm ≠ .revocable`.
- `hrev` is exactly what `srvMemberBoot_alloc`'s `hpfx` needs (`Alloc3.lean:138`,
  `absurd (Hklg.symm.trans h) hrev`). `hrun` replaces the hard-coded `lease.runCfg_none` (`:165`).
- The post gates `etcdKV` as `alloc1` does (`Alloc.lean:59`). `NewServerAlloc.lean` is untouched,
  as §1 promised.
- The interface diff (`interface/…/Alloc3.txt`) is exactly that.

**Findings.**

- **NIT (caller burden).** The gate is `if decide (lm ≠ .none) then True else etcdKV`
  (`Alloc3.lean:211, 339`). It makes each `.none` caller run a five-lemma `isimp` to recover
  `etcdKV` (`putget3/Main.lean:248`, `restart/Run.lean:242`).
  - `clusterAt`, in the same stage, gates by `match` (which reduces by iota).
  - It is consistent with `alloc1`, so either export an `alloc3`-side law (`if decide (.none ≠ .none)
    … = etcdKV …`), or accept the inconsistency and say why.
- **NIT (size).** `lm`/`hrun`/`hrev` follow the defaulted `(cmp := false) (cret := 0)`
  (`:188-191, 318-319`). Every caller must now pass `false 0` positionally
  (putget3 `Main.lean:243`, restart `Run.lean:237`), so the defaults serve no caller. Put `lm`,
  `hrun` and `hrev` before them, or drop the defaults.
- **NIT.** `memberBoot_of` takes both `lm` and `Hklg : γk.lm = lm` (`:115-116`). That is harmless
  (`memberBoot … lm` in the post names it); noted only as a binder that a `γk.lm`-indexed statement
  would not need.

## 4. `etcdstart.kv_lease_served_watch` (new)

**Good.**
- One private core, `kv_lease_served_core`, with `kv_lease_served` and `kv_lease_served_watch` as
  its two views (`ServedLease.lean:106, 375, 404`). So there is no second proof, which follows "one
  spec; a variant is a corollary of the one proof".
- The extra premise `hset` (the watch server's method set) is the watch chain's, and its source
  is `v3rpc.ServerMethodSets` (which StartMember holds).
- The post is exactly the shape `memberServed` keeps: `srvGoRes s` given back, the watch server
  and stream, and `noRefusalAt` from `grpcUp_noRefusal`.

**Findings.**
- **NIT.** `kv_lease_served` is not stated as a corollary of `_watch`. It cannot be, because it
  lacks `hset`. The core is the right factoring; the header could say that `_watch` is
  `kv_lease_served` plus the watch, and that callers without `hset` use the latter.
- The doubled `LeaseLeases` registration in the post at `.mono` is §2's NIT.

## 5. leasecatchup: Go, specs, closed theorem

**The Go code.** `examples/etcd/leasecatchup/leasecatchup.go` is a faithful rendering of §2.
- The only `panic` is at the check.
- The test (`leasecatchup_test.go:158-215`) fails unless member 3 is sent a snapshot and restores
  one holding the fillers. So the restore path is exercised in Go, as the Adequacy header claims.
- No Go bug found beyond the already-filed `issues/etcd-lease-id-mask-member-prefix.md`.
  - A filler colliding with `g1` makes Go return `ErrLeaseExists`, and `grant`'s post allows the
    error.
  - `leasePeersOk` holds of this program: the peer listener serves only `s.RaftHandler()`
    (`examples/lib/etcdstart/common.go:172`), so `/leases/internal` gets a 404.

**The panic check is discharged, not assumed.**
- `run`'s proof (`Proof/.../leasecatchup/run.lean:157-166, 252-290`) gets
  `∃ i, leaseGrantedAt E₃.γ.leases i g1` from `grant(c3)` at `etcdLeaseGrantSpec E₃.γ.leases`.
- It hands `[g1]` with that witness to every `leases(c3)` call at `etcdLeaseLeasesSpec
  E₃.γ.leases`, and obtains `mg.id ∈ ml.ids` for every successful listing.
- `listed` then returns `true` (`rw [decide_eq_true Hin]`), so the panic branch is dead.
- Note that the proof does not use "caught up" at all: the spec guarantees that every listing of
  member 3 after the grant lists `g1`, through the restore.
- That guarantee is proved inside the server: S2–S4's `Recover` premise is proved, and `sorryAx`
  is absent from the axioms. It rests on the trusted backend reads
  (`schema.MustUnsafeGetAllLeases.wp_proof` among the axioms), which are already in the
  leasekv/leaseexpiry bases.

**The closed theorem** (`Results.lean:62-94`, `Adequacy.lean:121`) is a meaningful no-panic claim
about this program.
- It covers every thread, servers included, in every `n`-step execution, with
  `v.isPanic = false` and not-stuck.
- Its premises are `k8s_compactor_partition_safe`'s, minus `steps`/`Hafter`, plus `Hlp`/`Hlne`, as
  §3 drafted.
- Each specific premise is discharged in `Adequacy.lean:165-174`: `cfgOk` by `clusterCfg_ok`, the
  bounds from `HT`/`HN`, `ServerMethodSets` by instance, and `AsTarget` by
  `rpctypesEtcdError_asTarget`.
- `Hlp` and `Hlne` are opaque deployment premises. `Hlp` is true here (above).
- `Hlne` inherits leasegrant's reading (`LessorBackend.lean:61-64`): the premise is read over the
  model's executions after `Main` returns too. That is the approved precedent, not new here.
  - With a TTL of 3600 s and a run of a few seconds in Go (plan, Go first: 1.3–7.6 s), the
    real-run reading holds.
  - Partition-induced `Promote`s only move expiries later.
- I could not verify independently that no execution of the model sends on `expiredC`. That is
  inherited, and **uncertain**.

**Findings.**

- **SHOULD-FIX (pure premises in the precondition).** Every new spec states its pure premises as
  Lean implications, against the principle the user set on 2026-11-03:
  - `run.spec` (`Spec/.../leasecatchup/run.lean:57-64`);
  - `Main.spec` (`Main.lean:36-43`);
  - `grant.spec`, `leases.spec` (the `errors.AsTarget` premise, `grant.lean:44`, `leases.lean:43`).
  - These specs are new and unfrozen, so conversion is cheap now: `⌜BootFacts …⌝ ∗ … ∗
    ⌜leasePeersOk ∧ lease.leasesNoExpiry⌝` in the `{{ … }}`.
  - If the sibling leasegrant `Main` shape is kept on purpose, say so in the header.
- **NIT.** `run.lean:23` paraphrases `leasesNoExpiry` as "no lease the cluster grants expires". The
  premise is "no lease of *any lessor the program creates* … (granted, or reloaded by `Recover`)"
  (`LessorBackend.lean:50-57`). Its own docstring records that the narrower wording was refuted.
  The Adequacy header (`:16-17`) repeats the narrow paraphrase. Quote the premise's own wording.
- **NIT.** `etc/tcb-collections/leasecatchup.txt:9` still says "Draft (pass 2(b)): the `sorry`s are
  cluster3's StartMember/StartCluster". There are none at `HEAD`, and the baseline lines are
  uncommitted.
- `config`, `grant`, `leases` and `listed` are good: each mirrors its Go body and passes the
  caller's `Q` through (`□ ▷ Spec req Q`). `listed` returns `decide (id ∈ ids)`, the exact Go
  result.

## 6. Callers (putget3, partition, restart, k8s compactorp)

**Their statements are unchanged.** `git diff lean...lease-mm -- Spec/` touches only cluster3's and
leasecatchup's specs. The proofs change only by:
- passing `.none` with `lease.runCfg_none`, `(by decide)` and `(fun h => absurd rfl h)`;
- `isimp only [cluster3.memberAt_none]` in place of `iunfold memberAt`;
- the `alloc3` gate's `isimp` (§3 NIT).

One meaning change sits outside the statement text: the trust base of `etcd_partition_safe` and
the k8s compactor's results grew by two axioms (§1, SHOULD-FIX).

## Ranking by need of revision

1. **`cluster3/Defs.lean`** (SHOULD-FIX ×3: no `.mono` elimination law, so the first client
   unfolds six definitions; `servedRegs`'s inline copy of `etcdKVAt` with a `rest` continuation;
   the missing `etcdLeaseServedAt_persistent`; NIT: `clusterAt`'s duplicated conjunct).
2. **`cluster3.StartMember`/`StartCluster`** (SHOULD-FIX: the trust-base growth of the `.none`
   closed results needs the user's explicit acknowledgement and committed baselines; NITs: stale
   "granting no lease"/"KV and watch" text, implication premises).
3. **leasecatchup specs** (SHOULD-FIX: pure premises as implications in new specs; NITs: the
   `leasesNoExpiry` paraphrase, the stale tcb header). The closed theorem itself is sound and
   non-vacuous as far as I could check.
4. **`Alloc3`** (NITs: the `if decide` gate costs callers a 5-lemma simp; defaults made useless by
   the trailing `lm`).
5. **`kv_lease_served_watch`** (NIT only).
6. **Callers**: no revision needed.
