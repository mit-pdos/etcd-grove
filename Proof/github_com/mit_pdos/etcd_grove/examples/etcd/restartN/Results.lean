/-
**restartN's results** (`notes/restartN-plan.md`, 2026-11-15): `restartN_Main` (`MainLinked.lean`'s `wp_Main`)
and the closed theorem `etcd_restartN_safe` (statement approved by the user, 2026-11-15, via etcd-grove-81, with
`3 ≤ k ≤ 1000`; `notes/restartN-draft.md`), with `#print axioms` of each.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Adequacy
public import Robustness.Statement

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_restartN.wp_Main`), for every `k ≤ 1000`. -/
theorem restartN_Main [go_etcd_io.etcd.cache.v3.Assumptions] :
    etcd_restartN.Main.spec (GF := GF) (hG := hG) :=
  etcd_restartN.wp_Main

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr
variable [go_gctx : GoGlobalContext]

/-- **The restart example with `k` members is safe, in the operational semantics, for every member
count `3 ≤ k ≤ 1000`** (approved by the user, 2026-11-15, via etcd-grove-81). It generalizes
`etcd_restart3_safe` to `k` members.

The verified etcd is the fork `upamanyus/etcd` at `6e8f0c004` (`etc/goose.py`'s pin): `goose-lean` with
the deferred in-window merge (D-A0-1), and raft v3.7 with the fixes of `notes/STATUS.md`, as for
`etcd_restart3_safe`.

The program (`examples/etcd/restartN`, `restartN.go`): its package's initialization, then `Main(k)`:
`k` etcd members started in-process (`etcdstart.Members("restartN", k, 29000, 30000)`: member `i` named
`restartN-i`, peer address `127.0.0.1:(29000+i)`). **The start mirrors `etcdstart.StartMembers`' steps**
(the initial cluster's map, then per member in order: the server built, its peer address listened on and
served, the server started) **but serves each member's peer address, for the whole run, through the
program's own handler `raftSwap`** (which forwards each request to the current incarnation's raft
handler) instead of its raft handler directly. Snapshot settings are `SnapCount = SnapCatchUp = 1`. Then:
`N1 = 5` sequential `Put`s of distinct keys through member `0`'s own API (member `0` may be a follower,
which forwards the proposal); a follower other than member `0` stopped gracefully (`HardStop`, after a
wait until it applied the `k` bootstrap entries): member `k - 1`, or member `k - 2` if member `k - 1`
sees itself as leader; `N2 = 20` more `Put`s through member `0`; the stopped member started again in the
same process on its data directory and at its addresses (etcd restarts it from its WAL, past a snapshot
record; it may be caught up by a leader's merged snapshot), its peer handler swapped to the new
incarnation's before it starts; a wait until it knows a leader; one linearizable `Range` of `["k", "l")`
through its own API (through the read index); a panic unless the `Range` returned exactly the `25`
pairs, in order, each at version `1`, at revision `26`.

From a fresh state, for every real execution of `n` steps: if `Main` returns, it returns unit; no
thread is stuck, and no thread has ended in a panic. So: if every `Put`, the restart and the `Range`
succeed, the `Range` returns exactly the 25 writes, each applied once, with its value, and nothing else.

**The range of `k`.** `3 ≤ k`: at `k = 2` the program is safe too (`Main.spec` holds for every
`k ≤ 1000`), but a real run never reaches the check (the one remaining member is not a quorum, so the
writes while member `1` is down time out); `k = 1` is restart1's case (`etcd_restart1_safe`: one member,
no follower to stop). No parity premise. `TestRun` in `restartN_test.go` runs `k` from {3, 5, 7} and
requires the snapshot catch-up.

**What it does not say** (restart3's).
- *Restart is a graceful stop in the same process:* not a kill, a SIGKILL or a power loss.
- *What the check does not compare:* the keys' create and mod revisions, their leases, the response's
  other header fields.
- *Liveness.* Any step may fail with an error, and `Run` then returns without a check.
- *One restart, of a follower, after the bootstrap entries are applied;* the chosen member may have
  become leader since the test: the theorem covers that run too.
- *No gRPC, no client:* the writes and the read are in-process calls.
- A request that reached the stopped incarnation's raft handler before the swap may still run in it
  after the stop: the proof covers it.

**Its hypotheses**, each with why it is true of the real run:
- `Hctx` (`ContextReadErrs`): `context.Canceled`'s and `DeadlineExceeded`'s method facts.
- `k`, `hk3`, `hk`: the member count, `3 ≤ k ≤ 1000` (`1000` keeps the ports in range and the peer and
  client ranges apart).
- `ids`, `Hlen`, `Hbf` (`BootFacts`, putgetN's): the `k` member ids in the members' order (their 16 low
  bits distinct and not `0`), the peers in `bootstrap`'s order (a permutation of them) and the bootstrap
  log, as Go computes them; at the token `restartN-1440` `TestMemberIDs` checks the ids for every
  `k ≤ 1000`.
- `Haf`, `Hbuq`, `Hdbo`: sizes of the auth records, the backend's quota, the WAL's and the disk's saves.
- `HNs` (`namesUnclaimed`): the read package's metric names are claimed by no one else at start.
- `HAs` (`addrsUnclaimed`): the `k` peer addresses are free at start; no client address is served.
- `HDs` (`dataDirsAbsent`): the `k` data directories do not exist at start.
- `HEnv` (`verifyEnvOff`): `ETCD_VERIFY` is unset (every incarnation).
- `Hprem` (`etcd_restartN.premises`, at every ghost-state instance): `bootstrapContract` for every
  member's first start; `bootMarshal` and the common names-only contracts; **N1,
  `bootstrapRestartContract`, for the two members that may be stopped** (`k - 2` and `k - 1`), its text
  unchanged.
- `σ`, `Hinit`, `Hthreads`, `Hlctx`: a fresh state with one thread.
- `Hn` (`n + 2 ≤ 2 ^ 28`): the execution's length.

**World assumptions it rests on without a hypothesis**: restart3's (request-id freshness across the two
incarnations, the graceful file model, the rest of the trust base, `etc/tcb-collections/restartN.txt`).
No listener close is assumed: the peer handler swap is proved. -/
theorem etcd_restartN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
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
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([restartNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_restartN_adequate Hctx k hk3 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hdbo HNs HAs HDs HEnv n Hprem
    σ g Hfs Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

/-- **`etcd_restartN_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_restartN_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
theorem etcd_restartN_robust
    [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restartNGF, ContextReadErrs (GF := restartNGF) (hG := heapAtRN hG lctx))
    (k : Nat) (hk3 : 3 ≤ k) (hk : k ≤ 1000) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hlen : ids.length = k) (Hbf : etcd_restartN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed (restartNProgram k) restartNNames)
    (HAs : addrsUnclaimed (restartNProgram k) (etcd_restartN.restartNAddrs k))
    (HDs : dataDirsAbsent (restartNProgram k) (etcd_restartN.restartNDirs k))
    (HEnv : verifyEnvOff (restartNProgram k))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC restartNGF,
      ⊢ etcd_restartN.premises (GF := restartNGF) (hG := heapAtRN hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) :
    Robustness.Robust [] [(restartNProgram k, σ)] g (2 ^ 28 - 1) :=
  Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
    (etcd_restartN_safe
      Hctx k hk3 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hdbo HNs HAs HDs HEnv n
      (Hprem n (by omega)) σ g Hfs hf.1 hf.2.1 hf.2.2 κs t2 σ2 Hsteps (by omega)).2

end adequacy

#print axioms restartN_Main
#print axioms etcd_restartN_adequate
#print axioms etcd_restartN_safe

end EtcdGrove
end Perennial
