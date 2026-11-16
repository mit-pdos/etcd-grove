# Draft: `raft_kvreconfN_porcupine_safe` (kvraftN, R2; for the user's review)

Status: **approved by the user, 2026-11-16, via etcd-grove-02, as drafted; linked** (kvreconf's `Adequacy.lean`,
`AdequacyLinked.lean`, `Results.lean`). Scope: `notes/kvraftN-scope.md`, "kvreconf and kvdurable: two options",
(R2). Modeled on `raft_kvN_porcupine_safe` (kv's `Results.lean`, approved 2026-11-16) and on
`raft_kvreconf_porcupine_safe` (kvreconf's `Results.lean`), whose text stays unchanged.

## The Lean text

To be added to `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/Adequacy.lean` (the program,
and `kvreconfN_adequate_of` from `MainN.spec`, as kv's `kvN_adequate_of`), `AdequacyLinked.lean`
(`raft_kvreconfN_adequate`, from `MainN`'s linked result) and `Results.lean` (the closed statement below).

```lean
/-- The store's program on `k` voters: the package's initialization, then `MainN(k)`. -/
def kvreconfProgramN [GoSemanticsFunctions] (k : Nat) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.MainN) #(W64 (k : Int))

/-- **The reconfiguring store's randomized linearizability test never fails, on any number of
voters** (`raft_kvreconfN_adequate`, `AdequacyLinked.lean`; kvraftN): for every member count
`1 ≤ k ≤ 1000`, every real execution of `kvreconfProgramN k` -- the store package's
initialization, then `MainN(k)`: a cluster of random options on the bootstrap voters `1 … k`, which
may start up to `k + 4` replicas, 4 clients of 100 random `Put`s, `Get`s and `Read`s, one to three
proposers of configuration changes and leadership disruptions, porcupine's check of the trace, and
a panic unless it answers `Ok` -- from a fresh state with one thread, of `n < 2^61` steps, has no
stuck thread and no thread that ended in a panic: porcupine always answers `Ok`.
`raft_kvreconf_porcupine_safe` is `Main()` (one to five voters drawn at random, up to 9 replicas);
nothing below `2^59` bounds `k` in the proof (`MainN.spec`), `1000` is the bound of the paper's
figure. -/
theorem raft_kvreconfN_porcupine_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]
    [hLog : log.NewModel]
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvreconfProgramN k], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  raft_kvreconfN_adequate k hk1 hk σ g Hlctx Hinit Hthreads n Hn κs t2 σ2 Hsteps

#print axioms raft_kvreconfN_porcupine_safe
```

(It sits in a `section closedN` with the local instances `trivialExts …` and `[go_gctx : GoGlobalContext]`,
as the two theorems it is modeled on.)

## In plain English

**What it says.** Pick any number of voters `k` from 1 to 1000. Run the Go program "initialize the
`kvreconf` package, then call `MainN(k)`" from a fresh machine with one thread, for any number of
steps below `2^61`, under any interleaving the scheduler picks and any outcome of the random choices
and of the simulated network. Then at every point: if the main thread has finished it returned
normally (`()`), no thread is stuck, and no thread has panicked. Since `MainN` panics exactly when
porcupine rejects the history it recorded, this means porcupine always answers `Ok`: every history
the clients observe is linearizable against a sequential key-value map.

**The program, `MainN(k)`** (`examples/raft/kvreconf/check.go`). It builds `RandomConfigN(k)`:
`RandomOptionsN(k)` -- `RandomOptions()`' random raft options (pre-vote, check-quorum,
step-down-on-removal, message size and inflight limits), with `Voters = k` and `MaxReplicas = k + 4` --
4 clients of 100 operations each, and 1 to 3 configuration-change proposers. `Run` starts a cluster
of raft nodes bootstrapped with voters `1 … k`, connected in process by a network that drops,
duplicates, delays and reorders messages; replicas snapshot and compact at random. Concurrently, the
clients issue random `Put`s, `Get`s (through the log) and `Read`s (by read index) on keys `a`, `b`,
`c`; the proposers propose random configuration changes (add a voter or a learner, remove, through
joint configurations or not; a fresh id starts a new replica, up to `k + 4` started in all), and a
disrupter moves leadership (transfers, campaigns, `ForgetLeader`). When the
clients are done, porcupine checks the trace; `MainN` panics unless it says `Ok`, then stops the
cluster.

**Every premise.**
- `k`, `1 ≤ k ≤ 1000`: the member count. `1000` is the figure's bound, the same as kvN's and etcd's
  N theorems; the proof's own bound is `k < 2^59` (`MainN.spec`: ids up to `k + 4` stay below raft's
  and the cluster's limits), so 1000 is not tight.
- `[go.Semantics]`, `[package_sem : …kvreconf.Assumptions]`, `[hLog : log.NewModel]`, `lctx`: as in
  both theorems it is modeled on -- any Go semantics, the translated bodies of the package and its
  imports, and the model of `log.New`. Nothing new.
- `σ`, `g`, `IsInit σ`, `σ.threads = 1`, `σ.goState.goLctx = lctx`: a fresh state (no package
  initialized), one thread. As before.
- `n < 2^61`, `RealNsteps n …`: any real execution of fewer than `2^61` steps. As before.

No new premise, axiom, `sorry` or trusted text: `MainN`'s proof is over the same trust base as
`Main`'s (`etc/tcb-collections/kvreconf.txt`), checked at linking.

**How it differs from `raft_kvN_porcupine_safe`.** Same shape and premises (`k`, `1 ≤ k ≤ 1000`, the
same conclusion); a different program: kvN's `MainN(k)` runs a fixed membership `1 … k` (no
configuration changes), 4 clients of 25 `Put`/`Get`/`Append`s; kvreconfN's runs the reconfiguring
store: random raft options, 100 operations per client, `Read` by read index, 1 to 3 proposers of
configuration changes, leadership disruptions, a faulty network, and replicas beyond the initial `k`
(up to `k + 4`). kvN's proof bounds `k < 2^62`, kvreconfN's `k < 2^59`; neither matters at 1000.

**How it differs from `raft_kvreconf_porcupine_safe`.** That theorem is about `Main()`, which draws
its voters at random (1 to 5) and may start up to 9 replicas; it has no `k`. This one fixes the
voter count to the caller's `k` and allows `k + 4` replicas (at `k = 5`, `Main`'s 9). Its text is
unchanged; its program's Go code changed in 18296d64f7 (the replica bound `maxReplicas = 9`, a
constant, became the field `Options.MaxReplicas`, which `RandomOptions` sets to 9), so `Main()`
behaves as before.

## Evidence

- Build (2026-11-16): every kvreconf and kvdurable module but `Link`, `Results`, `Adequacy*` (229
  kvdurable, the rest kvreconf: `/shared/tmp/kvraftN/targets.txt`) builds at 18296d64f7; no `sorry`
  or `axiom` in the changed files.
- Go: `TestMainN` (k from {1, 3, 5, 7}, `KVRECONF_MEMBERS` overrides) 20 runs under the 32G cap:
  all PASS, no panic (k = 1 ×4, 3 ×6, 5 ×4, 7 ×6; 1.5 to 15 s a run; `/shared/tmp/kvraftN/kvreconf-runs20.txt`).
