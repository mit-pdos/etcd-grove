/-
**restart1's results** (restart S7.5, 2026-11-14): `restart1_Main` (`MainLinked.lean`'s `wp_Main`) and the
closed theorem `etcd_restart1_safe` (its statement and docstring as frozen and approved by the user,
2026-11-14, `notes/restart-s7-freeze.md`, revision 2), with `#print axioms` of each.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Adequacy
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_restart1.wp_Main`). -/
theorem restart1_Main [go_etcd_io.etcd.cache.v3.Assumptions] :
    etcd_restart1.Main.spec (GF := GF) (hG := hG) :=
  etcd_restart1.wp_Main

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr
variable [go_gctx : GoGlobalContext]

/-- **The one-member restart example is safe, in the operational semantics.**

The program (`examples/etcd/restart1`): its package's initialization, then `Main()`: one etcd member
started in-process; `NPuts = 11` sequential `Put`s of distinct keys `key(i) ↦ value(i)` through the
server's own API (`EtcdServer.Put`); a wait until it applied the bootstrap entry; a graceful stop
(`HardStop`); the member started again in the same process on the same data directory (etcd restarts
it from its WAL, past a snapshot record); a wait until it knows a leader; one linearizable `Range` of
`["k", "l")` through its own API (`EtcdServer.Range`); a panic unless the `Range` returned exactly the
`NPuts` pairs, in order. From a fresh state, for every real execution of `n` steps: the main thread's
result, if it has one, is `#()`, no thread is stuck, and no thread has ended in a panic. So: whenever
every `Put` was acknowledged and the restarted member answered the `Range`, every acknowledged write
was applied exactly once (its key at version `1`, the store at revision `1 + NPuts`), with its value,
and nothing else is in the range.

**What it does not say.**
- *Restart is a graceful stop in the same process (N2).* The stop is etcd's `HardStop` (a stop
  without coordination with other members; with one member there is no leadership to transfer, which
  is its only difference from `Stop`): when it returns, the server's goroutines have exited and its
  files (WAL, snapshots, backend) are closed, and the restarted member reads the files that stop
  left, through the same page cache. The theorem does not cover a kill, a SIGKILL, or a power loss.
- *What the check does not compare:* the keys' create and mod revisions, and their leases (all `0`
  here); the response's other header fields.
- *Liveness.* Any step may fail with an error (a `Put`, the restart, the `Range`), and `Run` then
  returns without a check. The theorem says nothing in those runs, and nothing about the waits ending.
- *One member, no network.* No peer, no snapshot sent, no gRPC served, no client: the writes and the
  read are in-process calls. Three members (`restart3_safe`) need R2s-A.
- *One restart.* Not many restarts, not a restart during the writes.

**Its hypotheses**, each with why it is true of the real run:
- `Hctx` (`ContextReadErrs`): `context.Canceled`'s and `DeadlineExceeded`'s method facts, from
  `context`'s package fact (putget's).
- `Hbf` (`BootFacts`): the member id and the bootstrap log, as Go computes them from the
  configuration (`TestMemberID` in `restart1_test.go` prints the id; its low 16 bits are not `0`).
- `Haf` (`authRecordsFit`), `Hbuq` (`apply.backendUnderQuota`): sizes of the auth records and the
  backend's quota, as in putget (the run writes 11 small keys).
- `Hdbo` (`storage.diskOk`): no `Save` to the WAL fails and the WAL is created (a failed `Save` ends
  in `lg.Fatal`); also the WAL's size flag F8, graceful-only, true here. `restart1` is the first closed
  theorem to use its stop-side parts: the disk snapshot's save and release (`SnapCount = 1`), the
  WAL's close and bbolt's close at the stop (each failure is logged as fatal or returned on a path
  that ends the run).
- `HNs` (`namesUnclaimed`): the program's metric names (`initNames`: its closure's registering packages', mustreg 2026-11-20) are claimed by no one else at start.
- `HDs` (`dataDirsAbsent [restart1.etcd]`): the data directory does not exist when the program
  starts (the test runs in a fresh `t.TempDir()`).
- `HEnv` (`verifyEnvOff`): `ETCD_VERIFY` is unset for the run (both incarnations).
- `Hprem` (`etcd_restart1.premises`, at every ghost-state instance):
  - `bootstrapContract` for the first start (names-only `bootstrap`, D13b; its inherited `#Hmembers`
    flaw, G6/S11, as in every closed theorem);
  - `bootMarshal` (`proto.Marshal` of the bootstrap log), and the raft wrapper's names-only
    contracts (`rnLoggerZapOk`, `rnTimeoutDetectorOk`, `rnNewStorageOk`), as in putget;
  - **N1: `bootstrapRestartContract`** (`etcdstart.bootPremiseR`): Go's `bootstrap` on the stopped
    data directory (`wal.Open`, `ReadAll`, the snapshot load, the backend open, `cl.Recover`) yields
    `bootOkR`: the WAL handle with exactly the stopped records, the purge right, the image's backend
    at its consistent index. Inside it, the WAL's read facts I1-I4 (`walReadFacts`) and the
    graceful-only `i ≤ σ.commit` (F6, `rnRestartOk`'s marked conjunct). Accepted by the user
    (2026-11-14); `restart1_test.go` runs this path (20/20 passed; in 19 a WAL snapshot record at
    index 14 and the backend at consistent index 15, one entry replayed and skipped; in 1 the
    consistent index was the WAL's last entry).
- `σ`, `Hinit`, `Hthreads`, `Hlctx`: a fresh state with one thread.
- `Hn` (`n + 2 ≤ 2 ^ 28`): the execution's length (the thread bound and, with `N = n + 1`, the
  receipt bounds and the backend's write budget).

**World assumptions it rests on without a hypothesis** (in the trust base, listed here):
- **Request-id freshness across the two incarnations**: the trusted `Generator.Next`
  (`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`) assumes no other generator issued its id. False
  if the clock goes back, if the restart falls in the same millisecond, or if more than 256 ids per
  millisecond were issued since the previous start (`nonissues/etcd-request-id-restart-reuse.md`).
  Accepted by the user (2026-11-11). *How it bears here:* each incarnation's generator starts at its
  member-id prefix and its start time in milliseconds shifted by 8 bits, and counts up by one per id.
  The restarted generator could reissue an id of the first only if the first issued, since its own
  start, more than 256 ids per millisecond of the time between the two starts, or the clock went
  back. A reused id would let the restarted member match a replayed entry to a request it did not
  make (the wait registry, the proposal ids). In the test runs the first incarnation issues a few
  dozen ids (11 puts, the internal requests) over about a second before the restart: far below 256
  per millisecond.
- The restart reads the stopped files through the disk image's tokens: the WAL files
  (`wal.stopImage`, over the axiomatized `walFiles` token: the graceful file model, "the files a
  graceful stop in one process leaves"), the WAL directory's purge right (`walPurgeRight`), the
  snapshot directory (`srvFiles`) and the backend file (`backend.fileHolds` of `backendPathOf`, the
  claim on its name with its contents `backend.Data`; until S5 also the opaque `backend.pathOwn`).
- The rest of the existing trust base (`etc/tcb-collections/restart1.txt` will list it). -/
theorem etcd_restart1_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restart1GF, ContextReadErrs (GF := restart1GF) (hG := heapAtR1 hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_restart1.BootFacts id ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed restart1Program restart1Names)
    (HDs : dataDirsAbsent restart1Program [go!"/tmp/etcd-grove-data/restart1.etcd"])
    (HEnv : verifyEnvOff restart1Program)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC restart1GF,
      ⊢ etcd_restart1.premises (GF := restart1GF) (hG := heapAtR1 hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [go!"/tmp/etcd-grove-data/restart1.etcd"])
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([restart1Program], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_restart1_adequate Hctx id ctxs boot Hbf Haf Hbuq Hdbo HNs HDs HEnv n Hprem σ g Hfs HWal Hlctx Hinit
    Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms restart1_Main
#print axioms etcd_restart1_adequate
#print axioms etcd_restart1_safe

end EtcdGrove
end Perennial
