# restartN: the statement of `etcd_restartN_safe` (draft for review, 2026-11-15; HARD STOP before linking)

Branch `restartN` (worktree `/shared/etcd-grove-restartN`). Plan: `notes/restartN-plan.md`. `Main.wp_proof` is proved
(no `sorry`, no axiom, no trusted text added; targeted `lake build` of every module of the example, kernel included).
Nothing is linked yet: no `MainLinked`, `Adequacy`, `Results`, `PkgTable`/`Init`, collection.

## The theorem in plain words

The verified etcd is the fork `upamanyus/etcd` at `6e8f0c004` (A-g: the deferred in-window merge) and raft v3.7 with the
fixes of `notes/STATUS.md`, as for `etcd_restart3_safe`.

**The program** (`examples/etcd/restartN`): its package's initialization, then `Main(k)`: `k` etcd members started
in-process (`etcdstart.Members("restartN", k, 29000, 30000)`: member `i` named `restartN-i`, peer address
`127.0.0.1:(29000+i)`; each started as `etcdstart.StartMembers` starts them, in order, but with its peer address served for
the whole run by the program's own handler `raftSwap`, which forwards each request to the current incarnation's raft
handler; snapshot settings `SnapCount = SnapCatchUp = 1`); `N1 = 5` sequential `Put`s of distinct keys through member
`0`'s own API (member `0` may be a follower, which forwards the proposal); a follower other than member `0` stopped
gracefully (`HardStop`, after a wait until it applied the `k` bootstrap entries): member `k - 1`, or member `k - 2` if
`k > 2` and member `k - 1` sees itself as leader; `N2 = 20` more `Put`s through member `0`; the stopped member started
again in the same process on its data directory and at its addresses (its peer handler swapped to the new incarnation's
before it starts); a wait until it knows a leader; one linearizable `Range` of `["k", "l")` through its own API; a panic
unless the `Range` returned exactly the `25` pairs, in order, each at version `1`, at revision `26`. `Main(k)` for
`k < 2` returns at once.

**The claim**, for every member count `3 ≤ k ≤ 1000` (approved by the user, 2026-11-15, via etcd-grove-81; no parity premise): from a fresh state, for every real execution
of `n` steps, if `Main` returns it returns unit; no thread is stuck, and no thread has ended in a panic. So: if every
`Put`, the restart and the `Range` succeed, the `Range` returns exactly the 25 writes, each applied once, with its value,
and nothing else in the range.

**What it does not say** (restart3's list, unchanged): restart is a graceful stop in one process (not a kill, SIGKILL or
power loss); the check does not compare create/mod revisions, leases or other header fields; no liveness (any step may
fail and `Run` returns without a check; at `k = 2` the writes while member 1 is down cannot commit, so a real run never
reaches the check: TestRun at `RESTARTN_MEMBERS=2` returns before it); one restart, of a follower chosen after the
bootstrap entries are applied (the chosen member may have become leader since: covered); no gRPC, no client; a request
that reached the stopped incarnation's handler before the swap may still run in it (covered by the proof).

## The statement (Lean shape, to be written in `Adequacy.lean`/`Results.lean` at linking)

```lean
theorem etcd_restartN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restartNGF, ContextReadErrs (GF := restartNGF) (hG := heapAtRN hG lctx))
    (k : Nat) (hk3 : 3 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_restartN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed (restartNProgram k) restartNNames)
    (HAs : addrsUnclaimed (restartNProgram k) (etcd_restartN.restartNAddrs k))
    (HDs : dataDirsAbsent (restartNProgram k) (etcd_restartN.restartNDirs k))
    (HEnv : verifyEnvOff (restartNProgram k))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC restartNGF,
      ⊢ etcd_restartN.premises (GF := restartNGF) (hG := heapAtRN hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([restartNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

`restartNProgram k` = `restartN.initialize' #() ;; Main #(W64 k)` (putgetN's form).

## Every premise, against `etcd_restart3_safe` and `etcd_putgetN_safe`

| Premise | restartN | restart3 | putgetN |
|---|---|---|---|
| `Hctx` (`ContextReadErrs`) | same | same | same |
| `Hcec` (`ContextErrsClient`), `Hrf` (`grpcRepliesFit`), `[DialWithBalancerBody]` | **absent** (no client, no gRPC) | absent | present |
| `k`, `hk : k ≤ 1000` | putgetN's | — (three members) | same |
| `hk2 : 2 ≤ k` | **new** (putgetN has `1 ≤ k`); not used by the proof (`Main.spec` holds for every `k ≤ 1000`: `Run` returns at once for `k < 2`); kept so the statement does not claim the trivial `k ∈ {0, 1}` | — | `hk1 : 1 ≤ k` |
| ids | `ids : List w64`, `Hlen : ids.length = k` (putgetN's) | `id₁ id₂ id₃` | same as restartN |
| `Hbf` (`BootFacts`) | putgetN's `BootFacts ids …` (`BootCore` + `ps.Perm ids`); `TestMemberIDs` checks the ids at the token `restartN-1440` for every `k ≤ 1000` | putget3's `BootFacts id₁ id₂ id₃` | same as restartN, token `putgetN-1405` |
| `Haf`, `Hbuq`, `Hdbo` | same | same | same |
| `HNs` (`namesUnclaimed`) | same | same | same |
| `HAs` (`addrsUnclaimed`) | the `k` peer addresses (no client address served) | the 3 peer addresses | the `k` peer addresses and member 0's client address |
| `HDs` (`dataDirsAbsent`) | the `k` data directories `restartN-i.etcd` | 3 | `k` |
| `HEnv` (`verifyEnvOff`) | same (every incarnation) | same | same |
| `Hprem` (`premises`) | `bootstrapContract` for every member's first start (putgetN's `[∗list]` over `members k` and `ids`); **N1 (`bootPremiseR`, the restart contract) for the last `min 2 (k-1)` members** (`k - 2` and `k - 1`; member 1 at `k = 2`), its text unchanged; `bootMarshal`; `commonPremises` | `bootstrapContract` ×3, N1 for members 2 and 3 (1-based; the same two roles: the non-writing members, of which the stopped one is chosen), `bootMarshal`, `commonPremises` | `bootstrapContract` ×k, `bootMarshal`, `commonPremises` |
| `σ`, `Hinit`, `Hthreads`, `Hlctx`, `Hsteps`, `Hn` | same | same | same |

**No new kind of premise.** The only new hypothesis is `hk2` (a bound on `k`). N1's text (`bootstrapRestartContract`) and
the restart contract are unchanged; N1 is assumed for exactly the members `Run` may stop. Callee hypotheses at linking:
`rafthttp.bootCfg` for up to 1000 members (putgetN's `bootCfg_of_le`, landed), `mvcc.api.names_nonempty`/
`mvccReaders_split` (laws already linked by restart3): nothing new.

**Trust base (expected, measured at linking):** restart3's 530 axioms (it already contains `strconv.FormatUint.wp_proof`,
the only boundary `etcdstart.Members` adds), 0 sorries. No trusted text.

## Decisions requested (recommendation first)

1. **Range of `k`: `2 ≤ k ≤ 1000`** (recommended). Alternatives: `3 ≤ k` (excludes the `k = 2` case whose real runs never
   reach the check); no lower bound (true, but trivial at `k ∈ {0, 1}`). `k = 1` stays `etcd_restart1_safe`.
2. **The start: a local `startMembers` loop** (StartMembers' steps, each peer address served through `raftSwap`) — done
   this way (recommended): `etcdstart.StartMembers` serves the raft handler on its listener for good, so restarting
   through it would need the listener-close assumption (HS3) restart3 avoided. Alternatives: a new `etcdstart` function
   with swaps (rebuilds every example), or changing `StartMembers` (changes putgetN's and txnlinfaultsN's programs).
3. **N1 only for the two candidates** (recommended) vs for every member but 0 (simpler to state, more assumed).
4. **The name `etcd_restartN_safe`.**

## Verified so far
- Go: `TestMemberIDs` (every `k ≤ 1000`), `TestRun` 20/20 under the 32G cap (k=3: 8, k=5: 3, k=7: 9), every run with a
  merged snapshot sent and installed after the restart (required by the test) (`/shared/tmp/restartN/runs20.txt`).
- Lean: targeted `lake build` (64G cap) of `restartN.{Run,Main,startMembers,Dir,stop,put,check,build,newMember,raftSwap}`
  green, no `sorry` in the example (`/shared/tmp/restartN/build-s3.log`).
