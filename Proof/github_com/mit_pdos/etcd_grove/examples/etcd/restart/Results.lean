/-
**restart3's results** (restart3 C4, 2026-11-15): `restart3_Main` (`MainLinked.lean`'s `wp_Main`) and the
closed theorem `etcd_restart3_safe` (statement approved by the user, 2026-11-15, via etcd-grove-81), with
`#print axioms` of each.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Adequacy
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_restart.wp_Main`). -/
theorem restart3_Main [go_etcd_io.etcd.cache.v3.Assumptions] :
    etcd_restart.Main.spec (GF := GF) (hG := hG) :=
  etcd_restart.wp_Main

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr
variable [go_gctx : GoGlobalContext]

/-- **The three-member restart example is safe, in the operational semantics.**

The verified etcd is the fork `upamanyus/etcd` at `6e8f0c004` (`etc/goose.py`'s pin): `goose-lean` with
the deferred in-window merge (D-A0-1: the apply loop drops a merged snapshot that arrives while its
sender is inside its own replay window, and reports it failed, `ReportSnapshot`), and raft v3.7 with the
fixes of `notes/STATUS.md`.

The program (`examples/etcd/restart`, `restart3.go`): its package's initialization, then `Main()`:
three etcd members started in-process, each member's peer address served for the whole run by the
program's own handler (`raftSwap`, which forwards each request to the current incarnation's raft
handler); `N1 = 5` sequential `Put`s of distinct keys `key(i) ↦ value(i)` through member 1's own API
(`EtcdServer.Put`; member 1 may be a follower, which forwards the proposal); a follower other than
member 1 stopped gracefully (`HardStop`, after a wait until it applied the three bootstrap entries):
member 3, or member 2 if member 3 sees itself as leader; `N2 = 20` more `Put`s through member 1; the
stopped member started again in the same process on its data directory and at its addresses (etcd
restarts it from its WAL, past a snapshot record; the members compact their logs at
`SnapCount = SnapCatchUp = 1`, so it may be caught up by a leader's snapshot), its peer handler swapped
to the new incarnation's before it starts; a wait until it knows a leader; one linearizable `Range` of
`["k", "l")` through its own API (`EtcdServer.Range`, through the read index); a panic unless the
`Range` returned exactly the `25` pairs, in order, each at version `1`, at revision `26`.

From a fresh state, for every real execution of `n` steps: if `Main` returns, it returns unit; no
thread is stuck, and no thread has ended in a panic. So: if every `Put`, the restart and the `Range`
succeed, the `Range` returns exactly the 25 writes, each applied once (its key at version `1`, the store
at revision `1 + 25`), with its value, and nothing else in the range.

**What it does not say.**
- *Restart is a graceful stop in the same process (N2):* not a kill, a SIGKILL or a power loss.
- *What the check does not compare:* the keys' create and mod revisions, their leases, the response's
  other header fields.
- *Liveness.* Any step may fail with an error, and `Run` then returns without a check; nothing about
  the waits ending or the peers reconnecting.
- *One restart, of a follower, after the bootstrap entries are applied;* not a restart during the
  writes, not of the leader by choice (member 3 may lose leadership between the test and the stop: the
  theorem covers that run too).
- *No gRPC, no client:* the writes and the read are in-process calls.
- A request that reached the stopped incarnation's raft handler before the swap may still run in it
  after the stop: the proof covers it (the run keeps its own copy of the incarnation's serving
  resources; nothing is assumed of it).

**Its hypotheses**, each with why it is true of the real run:
- `Hctx` (`ContextReadErrs`): `context.Canceled`'s and `DeadlineExceeded`'s method facts (restart1's).
- `Hbf` (`BootFacts`): the member ids, the peers and the bootstrap log, as Go computes them from the
  configurations (putget3's; `TestMemberIDs` in `restart3_test.go` prints the ids).
- `Haf`, `Hbuq`, `Hdbo`: sizes of the auth records, the backend's quota, the WAL's and the disk's
  saves (restart1's, with its stop-side parts).
- `HNs` (`namesUnclaimed`): the read package's metric names are claimed by no one else at start.
- `HAs` (`addrsUnclaimed`): the three peer addresses are free at start (the closed-world clause the
  user accepted on 2026-11-14); no client address is served.
- `HDs` (`dataDirsAbsent`): the three data directories do not exist at start.
- `HEnv` (`verifyEnvOff`): `ETCD_VERIFY` is unset (every incarnation).
- `Hprem` (`etcd_restart.premises`, at every ghost-state instance): `bootstrapContract` for each
  member's first start (its inherited `#Hmembers` flaw, S11); `bootMarshal` and the common names-only
  contracts; **N1, `bootstrapRestartContract`, for members 2 and 3** (either may be the one stopped),
  its text as A1's approved Freeze leaves it.
- `σ`, `Hinit`, `Hthreads`, `Hlctx`: a fresh state with one thread.
- `Hn` (`n + 2 ≤ 2 ^ 28`): the execution's length (the thread bound, and with `N = n + 1` the receipt
  bounds and the backend's write budget `N + 7 + bootWB ≤ wbInit`; the levels `srvLevels` follow from
  the thread bound).

**World assumptions it rests on without a hypothesis** (in the trust base): request-id freshness across
the two incarnations (accepted 2026-11-11, `nonissues/etcd-request-id-restart-reuse.md`); the restart
reads the stopped files through the disk image's tokens (the graceful file model); the rest of the
existing trust base (`etc/tcb-collections/restart3.txt`). No listener close (HS3) is assumed: the
peer handler swap is proved. -/
theorem etcd_restart3_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restart3GF, ContextReadErrs (GF := restart3GF) (hG := heapAtR3 hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_restart.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed restart3Program restart3Names)
    (HAs : addrsUnclaimed restart3Program restart3Addrs)
    (HDs : dataDirsAbsent restart3Program
      [(etcd_restart.name₁ ++ go!".etcd"), (etcd_restart.name₂ ++ go!".etcd"), (etcd_restart.name₃ ++ go!".etcd")])
    (HEnv : verifyEnvOff restart3Program)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC restart3GF,
      ⊢ etcd_restart.premises (GF := restart3GF) (hG := heapAtR3 hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([restart3Program], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_restart3_adequate Hctx id₁ id₂ id₃ ps ctxs boot Hbf Haf Hbuq Hdbo HNs HAs HDs HEnv n Hprem σ g Hfs
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms restart3_Main
#print axioms etcd_restart3_adequate
#print axioms etcd_restart3_safe

end EtcdGrove
end Perennial
