/- Lean-first (no Rocq counterpart).

# `etcd/all`: the single-process closed etcd theorem, stated

`etcd_robust_single_process`: the closed theorem of `examples/etcd/all` (`notes/etcd-unified-scope.md`, the user's
decisions D1-D6 and N1-N7 of 2026-11-21) as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the machines
that may crash and restart and of those that never crash, each a fresh Go process, of fewer than `bound`
steps, no thread is stuck and none has an unrecovered panic). The program runs, in one process and at
once, eleven etcd examples, each on a cluster of its own, in four parts:

- **KV**: txnlinfaultsN's transactional workload on `k₁` members under a partition schedule of `n₁`
  steps (porcupine checks the history's linearizability); partition's watch workload on three members
  under a schedule of `n₂` steps (`MainWatch`: the watches see the writes); compactwatch's watches under the revision
  auto-compactor and compacted's Put then Get under the periodic one, on one member each; cache's watch
  cache under the periodic compactor, on one member;
- **Auth**: authN on `k₂` members (the principals' rights enforced at every member) and authlease on `k₃`
  (the lease rows of the auth checks);
- **Lease**: leaseN on `k₄` members (lease reads at every member) and leasecatchup on three (a lessor
  recovered from a snapshot);
- **Restart**: restartN on `k₅` members (a follower stopped and restarted, no acknowledged write lost)
  and restart1 (the one member stopped and restarted).

Each panics if its check fails; so no check fails, for every value of the program's arguments
(`MainChecked`, `TopLevelDefs.lean`'s `etcdProgram`; the pure-premises plan's P4, 2026-11-24): it runs the
examples when the member counts and workloads are in the ranges the proof covers (`ParamsOk`:
`1 ≤ k₁ ≤ 1000`, `1 ≤ k₂, k₃, k₄ ≤ 300`, `3 ≤ k₅ ≤ 300`, each workload's clients in `[0, 2^31)` and its
total operations below `2^60` or `2^62`), under fault schedules it draws itself (`cluster3.RandomSchedule`,
`n₁` and `n₂` random steps), and otherwise returns at once. Until then those ranges and the two
schedules (lists given to the program) were premises; the Go test `TestMainCheckedRun`
(`examples/etcd/all/checked_test.go`) shows the check passes and every part runs at `k = 3` with drawn
schedules, and `TestParamsOk` that `ParamsOk` agrees with the former premises on 200 000 boundary draws. It is to replace the
drivers' own closed theorems and the single examples' theorems they subsume (stage E4). What the
replaced theorems claimed and this one does not: authN's, authlease's, leaseN's and restartN's own
theorems claimed `k ≤ 1000`; here they run on at most 300 members (the user's decision N2: with the
tokens searched for `Hlow`, their `BootFacts` is checked only to 300 anyway); and partition's `Main`
theorem (porcupine's check of its workload on three members under a partition schedule) has no part
of its own: txnlinfaultsN runs the same workload and schedule, and covers it at `k₁ = 3`. leaseexpiryN is not in it (N1): its leases expire, which authlease's and leasecatchup's
premise `lease.leasesNoExpiry` (about every lessor of the process) excludes; it keeps its own theorem.
That premise is true of every run of this program, however long: authlease and leasecatchup, its only
drivers that grant leases, grant them with etcd's `MaxLeaseTTL` (9000000000 s, about 285 years).

**The single-process theorem** (2026-11-23, etcd-grove#28, `notes/single-process-restore.md`): retired at
the net swap (2026-11-22) as `etcd_robust`, whose name the distributed theorem took
(`Spec/.../examples/etcd/dist/`), and restored under this name. Since the swap `net` is the net extension's
(`GooseLang/Ext/Net`): the program runs over `etcdNetExts` (`[idIssueExt, fsExt, netExt]`,
`Proof/.../examples/lib/etcdstart/NetExts.lean`), the network starting with no connection and no listener
(`Robust`'s premises on the extensions' initial states), and the statement takes Net's hand-stated field
facts of `net`'s structs (`net.FieldAssumptions`, a semantic premise as `os.file.FieldAssumptions`).
`HAs` (`addrsUnclaimed`) is as before the swap: (a) no other process binds or dials the addresses (the
models' gRPC and HTTP traffic does not go through the net extension, so its closed network does not
cover it), (b) the program's own connections to them are its verified or trust-boundary clients'.

**What the file semantics assumes** (`etcdNetExts`, `Proof/.../examples/lib/etcdstart/NetExts.lean` and
`FsExts.lean`, and the file extension's `GooseLang/Ext/Fs/Impl.lean`; not premises of the statement, part
of the semantics it is stated over): no file operation fails with an I/O error (no `ENOSPC`, no `EIO`), and at
every `open(2)` the process holds fewer descriptors than its `RLIMIT_NOFILE`. At the bounds the process
runs up to 2,210 members in one process, so a deployment the theorem describes has room for every
member's WAL (each preallocates a 64 MB segment, `wal.SegmentSizeBytes`: about 141 GB at the bounds,
plus the members' bbolt files) and a descriptor limit above all members' files and sockets (rafthttp
keeps several connections per ordered pair of a cluster's members, so `k₁ = 1000` alone needs millions
of descriptors). A run that runs out of either is outside the semantics, and the theorem says nothing
of it; measured only at `k = 3` (`TestMainRun`).

This file only states it (to audit); the proof is to be in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`.

**The premises** are the union of the composed drivers' theorems': each cluster's member ids and
bootstrap log (`BootFacts`; authlease's ids also apart in 15 bits, `Hap`), the server's opaque workload and
environment premises once (`Haf`, `Hbuq`, `Hrf`, `Hdbo`), the lease premises of leaseN, authlease and
leasecatchup once (`Hlp`, `Hlne`), the program's addresses and data directories (all clusters', concatenated), `ETCD_VERIFY` off, each
cluster's named premises (`Hprem…`, at every step bound `n` with `n + 1 ≤ 2 ^ 48`, the bound the proof
uses), the file system's initial state and the
members' WAL areas (`HWal`, all clusters'); and one premise of the composition, `Hlow`: the 16 low bits of
the ids of the process's every member (all eleven clusters') are distinct, the precondition of the
trusted model of etcd's request-id generator (`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`: no two
generators of the process issue one id), checked at these bounds by `examples/etcd/all`'s `TestMemberIDs`
(with the drivers' tokens searched for it, 2026-11-21; at five clusters of 1000 no tokens make it hold).
The proof does not use it: it states the condition under which that trusted model is faithful (each
cluster's own `BootFacts` states it for that cluster, `BootCore.lowNodup`).
The counts are the program's `uint64` arguments, any value: the premises indexed by them (`Hlen…`,
`Hbf…`, `Hprem…`, `Hlow`) are stated at `uint.nat kᵢ`, and the addresses and data directories (`HAs`,
`HDs`, `HWal`) are `etcdProgAddrs`/`etcdProgDirs` (`TopLevelDefs.lean`): the clusters' at counts in
range, none outside, where `MainChecked` starts no member (as leaseexpiryN's `cluster k`, P6).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.compactwatch.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.compacted.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section adequacy

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

variable [go_gctx : GoGlobalContext]

/-- **`etcd_safe_single_process` as a robustness statement** (`Robustness.Robust`, `Robustness/Statement.lean`; see
the file header): the program alone on one machine that never crashes, a fresh Go process (`Robust`'s
premise), under `etcd_safe_single_process`'s other hypotheses: in every execution of fewer than `2 ^ 48` steps
along which fewer than `2 ^ 28` threads are live, no thread is stuck and none has an unrecovered
panic. -/
def etcd_robust_single_process.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]
    [log.NewModel]
    [_root_.Perennial.net.FieldAssumptions]
    -- (wal-nostorageok, 2026-11-21: for the premise `rnNewStorageOk`) `os`'s field steps
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    -- KV: txnlinfaultsN's cluster, `k₁` members
    (k₁ : w64) (ids₁ ps₁ : List w64) (ctxs₁ : List (List w8))
    (boot₁ : List LogEntry) (Hlen₁ : ids₁.length = uint.nat k₁)
    (Hbf₁ : etcd_txnlinfaultsN.BootFacts ids₁ ps₁ ctxs₁ boot₁)
    -- KV: partition's cluster (three members)
    (pid₁ pid₂ pid₃ : w64) (psP : List w64) (ctxsP : List (List w8)) (bootP : List LogEntry)
    (HbfP : etcd_partition.BootFacts pid₁ pid₂ pid₃ psP ctxsP bootP)
    -- KV: compactwatch's, compacted's and cache's one-member clusters
    (cwId : w64) (ctxsCW : List (List w8)) (bootCW : List LogEntry)
    (HbfCW : etcd_compactwatch.BootFacts cwId ctxsCW bootCW)
    (cId : w64) (ctxsC : List (List w8)) (bootC : List LogEntry)
    (HbfC : etcd_compacted.BootFacts cId ctxsC bootC)
    (kvId : w64) (ctxsK : List (List w8)) (bootK : List LogEntry)
    (HbfK : etcd_putget.BootFacts kvId ctxsK bootK)
    -- Auth: authN's cluster, `k₂` members, and authlease's, `k₃` (their ids apart in 15 bits)
    (k₂ : w64) (ids₂ ps₂ : List w64) (ctxs₂ : List (List w8))
    (boot₂ : List LogEntry) (Hlen₂ : ids₂.length = uint.nat k₂)
    (Hbf₂ : etcd_putgetN.BootFacts ids₂ ps₂ ctxs₂ boot₂)
    (k₃ : w64) (ids₃ ps₃ : List w64) (ctxs₃ : List (List w8))
    (boot₃ : List LogEntry) (Hlen₃ : ids₃.length = uint.nat k₃)
    (Hbf₃ : etcd_putgetN.BootFacts ids₃ ps₃ ctxs₃ boot₃) (Hap : leaseIdsApart ids₃)
    -- Lease: leaseN's cluster, `k₄` members, and leasecatchup's (three members)
    (k₄ : w64) (ids₄ ps₄ : List w64) (ctxs₄ : List (List w8))
    (boot₄ : List LogEntry) (Hlen₄ : ids₄.length = uint.nat k₄)
    (Hbf₄ : etcd_putgetN.BootFacts ids₄ ps₄ ctxs₄ boot₄)
    (lid₁ lid₂ lid₃ : w64) (psL : List w64) (ctxsL : List (List w8)) (bootL : List LogEntry)
    (HbfL : cluster3.BootFacts lid₁ lid₂ lid₃ psL ctxsL bootL)
    -- Restart: restartN's cluster, `k₅` members, and restart1's one member
    (k₅ : w64) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8))
    (boot₅ : List LogEntry) (Hlen₅ : ids₅.length = uint.nat k₅)
    (Hbf₅ : etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    (HbfR : etcd_restart1.BootFacts rId ctxsR bootR)
    -- the process's every member: their ids' 16 low bits distinct (idutil's trusted model)
    (Hlow : ((ids₁ ++ [pid₁, pid₂, pid₃, cwId, cId, kvId] ++ ids₂ ++ ids₃ ++ ids₄ ++
      [lid₁, lid₂, lid₃] ++ ids₅ ++ [rId]).map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    -- the server's workload and environment
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- peers answer `/leases/internal` as etcd's handler does or not with 200; no lease expires in the run
    (Hlp : leasePeersOk) (Hlne : lease.leasesNoExpiry)
    -- txnlinfaultsN's workload and its schedule's length, partition's watch workload and its
    -- schedule's length, cache's workload (any values: `MainChecked` checks them)
    (clients ops n₁ nw nops n₂ cnw cnops : w64)
    -- the program's addresses, data directories and environment
    (HAs : addrsUnclaimed (etcdProgram k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅)
      (etcdProgAddrs k₁ k₂ k₃ k₄ k₅))
    (HDs : dataDirsAbsent (etcdProgram k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅)
      (etcdProgDirs k₁ k₂ k₃ k₄ k₅))
    (HEnv : EtcdVerifyOff)
    -- each cluster's named premises
    (Hprem₁ : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_txnlinfaultsN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₁) n ids₁
          ps₁ ctxs₁ boot₁)
    (HpremP : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_partition.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n pid₁ pid₂ pid₃ psP ctxsP
          bootP)
    (HpremCW : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_compactwatch.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n cwId ctxsCW bootCW)
    (HpremC : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_compacted.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n cId ctxsC bootC)
    (HpremK : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_cache.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n kvId ctxsK bootK)
    (Hprem₂ : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_authN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₂) n ids₂ ps₂
          ctxs₂ boot₂)
    (Hprem₃ : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_authlease.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₃) n ids₃
          ps₃ ctxs₃ boot₃)
    (Hprem₄ : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_leaseN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₄) n ids₄ ps₄
          ctxs₄ boot₄)
    (HpremL : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ cluster3.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) etcd_leasecatchup.clusterCfg n
          lid₁ lid₂ lid₃ psL ctxsL bootL)
    (Hprem₅ : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_restartN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₅) n ids₅
          ps₅ ctxs₅ boot₅)
    (HpremR : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_restart1.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n rId ctxsR bootR)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world)
      (etcdProgDirs k₁ k₂ k₃ k₄ k₅)),
    Robustness.Robust [] [(etcdProgram k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅, σ)] g
      (threads := 2 ^ 28) (bound := 2 ^ 48)

end adequacy
end EtcdGrove
end Perennial

end
