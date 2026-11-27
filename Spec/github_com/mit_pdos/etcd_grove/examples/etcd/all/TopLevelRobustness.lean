/- Lean-first (no Rocq counterpart).

# `etcd/all`: the single-process closed etcd theorem, stated

`etcd_restart_robust_single_process`: the closed theorem of `examples/etcd/all` (`notes/etcd-unified-scope.md`, the user's
decisions D1-D6 and N1-N7 of 2026-11-21) as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the machines
that may crash and restart and of those that never crash, each a fresh Go process, of fewer than `bound`
steps, no thread is stuck and none has an unrecovered panic). The program runs, in one process and at
once, the **restart part**: restartN on `k₅` members (a follower stopped and restarted, no acknowledged
write lost) and restart1 (the one member stopped and restarted), each on a cluster of its own.

Each panics if its check fails; so no check fails, for every value of the program's argument
(`MainChecked`, `TopLevelDefs.lean`'s `etcdProgram`; the pure-premises plan's P4, 2026-11-24): it runs the
examples when the member count is in the range the proof covers (`ParamsOk`: `3 ≤ k₅ ≤ 300`), and
otherwise returns at once. The Go test `TestMainCheckedRun` (`examples/etcd/all/checked_test.go`) shows
the check passes and the part runs at `k₅ = 3`, and `TestParamsOk` that `ParamsOk` agrees with the former
premise around its bounds. restartN's own theorem claimed `k ≤ 1000`; here it runs on at most 300
members (the user's decision N2: with the tokens searched for `Hlow`).

**Until 2026-11-27** the program also ran the KV part (txnlinfaultsN, partition's watches, compactwatch,
compacted, cache), the Auth part (authN, authlease) and the Lease part (leaseN, leasecatchup), and
`etcd_leaseexpiryN_robust_single_process` was a theorem of its own; their workloads run in the
multi-machine deployments of `etcd_safe_nocrash` (`Spec/.../examples/etcd/dist/`), which replaced them
(rule 41; `notes/STATUS.md`, 2026-11-27). The restart part stays until `etcd_safe` with crashes is proved:
`Robust []` has no crash or restart, and this is the only proof that a stopped and restarted member keeps
acknowledged writes.

**The single-process theorem** (2026-11-23, etcd-grove#28, `notes/single-process-restore.md`): retired at
the net swap (2026-11-22) as `etcd_robust`, whose name the distributed theorem took
(`Spec/.../examples/etcd/dist/`), and restored under this name. Since the swap `net` is the net extension's
(`GooseLang/Ext/Net`): the program runs over `etcdNetExts` (`[idIssueExt, fsExt, netExt]`,
`Proof/.../examples/lib/etcdstart/NetExts.lean`), the network starting with no connection and no listener
(`Robust`'s premises on the extensions' initial states). (It took Net's hand-stated field facts of `net`'s
structs, `net.FieldAssumptions`, until the Go-model overlays S6, 2026-11-24, translated `net`'s structs.)
`HAs` (`addrsUnclaimed`) is as before the swap: (a) no other process binds or dials the addresses (the
models' gRPC and HTTP traffic does not go through the net extension, so its closed network does not
cover it), (b) the program's own connections to them are its verified or trust-boundary clients'.

**What the file semantics assumes** (`etcdNetExts`, `Proof/.../examples/lib/etcdstart/NetExts.lean` and
`FsExts.lean`, and the file extension's `GooseLang/Ext/Fs/Impl.lean`; not premises of the statement, part
of the semantics it is stated over): no file operation fails with an I/O error (no `ENOSPC`, no `EIO`), and at
every `open(2)` the process holds fewer descriptors than its `RLIMIT_NOFILE`. At the bound the process
runs up to 301 members in one process, so a deployment the theorem describes has room for every
member's WAL (each preallocates a 64 MB segment, `wal.SegmentSizeBytes`: about 19 GB at the bound, plus
the members' bbolt files) and a descriptor limit above all members' files and sockets (rafthttp keeps
several connections per ordered pair of a cluster's members). A run that runs out of either is outside
the semantics, and the theorem says nothing of it; measured only at `k = 3` (`TestMainRun`).

This file only states it (to audit); the proof is to be in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`.

**The premises** are the union of the two drivers' theorems': each cluster's member ids and bootstrap
log (`BootFacts`), the server's opaque workload and environment premises once (`Haf`, `Hbuq`, `Hdbo`),
the program's addresses and data directories (both clusters', concatenated), `ETCD_VERIFY` off, the
file system's initial state and the members' WAL areas (`HWal`, both clusters'); and one
premise of the composition, `Hlow`: the 16 low bits of the ids of the process's every member (both
clusters') are distinct, the precondition of the trusted model of etcd's request-id generator
(`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`: no two generators of the process issue one id),
checked at the bound by `examples/etcd/all`'s `TestMemberIDs`. The proof does not use it: it states the
condition under which that trusted model is faithful (each cluster's own `BootFacts` states it for that
cluster, `BootCore.lowNodup`).
**`bootstrap`'s contracts** (premises to axioms, 2026-11-27; until then the Iris premises `Hprem₅` and
`HpremR`, each cluster's named premises): restart1's first start and both clusters' restarts are
`bootstrap`'s interim axioms' (`bootstrap.wp_proofOne`, `bootstrap.wp_proofRestart`, at Go's values), so the
statement takes the pure facts that the ids, peers, contexts and directories it names are what `bootstrap`
computes (`Hbg₅`, `HbgR`: putget's `BootGo1` per member) and `GODEBUG` `fips140` off (`Hfips`, `crypto/sha1`'s
setting, as the distributed statements). One Iris premise is left, `Hprem₅`: restartN's members' first-start
contracts (`etcd_restartN.bootPremises`, `bootstrapContract` at each), at every step bound `n` with
`n + 1 ≤ 2 ^ 48`. No spec of `bootstrap` covers a first start of several members in one process yet: there
`isMemberBootstrapped` sends `GET /members` to the members already serving, whose answer no protocol of the
in-process HTTP model constrains (`notes/specs-only/ledger.md`, 2026-11-24, `isMemberBootstrapped.spec`).
The count is the program's `uint64` argument, any value: the premises indexed by it (`Hlen₅`, `Hbf₅`,
`Hprem₅`, `Hlow`) are stated at `uint.nat k₅`, and the addresses and data directories (`HAs`, `HDs`,
`HWal`) are `etcdProgAddrs`/`etcdProgDirs` (`TopLevelDefs.lean`): the clusters' at a count in range,
none outside, where `MainChecked` starts no member.
`cache_sem` (the Goose type assumptions of etcd's `cache` package, which restartN's and restart1's
triples take) was part of `package_sem` until 2026-11-27 (`etcdall`'s `Assumptions` reached it through
the cache driver's package); with that driver gone it is stated on its own, as leaseexpiryN's theorem did.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Boot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
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

/-- **`etcd_restart_safe_single_process` as a robustness statement** (`Robustness.Robust`, `Robustness/Statement.lean`; see
the file header): the program alone on one machine that never crashes, a fresh Go process (`Robust`'s
premise), under `etcd_restart_safe_single_process`'s other hypotheses: in every execution of fewer than `2 ^ 48` steps
along which fewer than `2 ^ 28` threads are live, no thread is stuck and none has an unrecovered
panic. -/
def etcd_restart_robust_single_process.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    -- restartN's cluster, `k₅` members, and restart1's one member
    (k₅ : w64) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8))
    (boot₅ : List LogEntry) (Hlen₅ : ids₅.length = uint.nat k₅)
    (Hbf₅ : etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    (HbfR : etcd_restart1.BootFacts rId ctxsR bootR)
    -- (premises to axioms, 2026-11-27) `bootstrap`'s values are Go's: restartN's members' and restart1's
    -- member's ids, peers, contexts and directories, as `bootstrap` computes them from each configuration
    (Hbg₅ : etcd_restartN.BootGoN (uint.nat k₅) ids₅ ps₅ ctxs₅)
    (HbgR : etcd_restart1.BootGo rId ctxsR bootR)
    -- the process's every member: their ids' 16 low bits distinct (idutil's trusted model)
    (Hlow : ((ids₅ ++ [rId]).map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    -- the server's workload and environment
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    -- the program's addresses, data directories and environment
    (HAs : addrsUnclaimed (etcdProgram k₅) (etcdProgAddrs k₅))
    (HDs : dataDirsAbsent (etcdProgram k₅) (etcdProgDirs k₅))
    (HEnv : EtcdVerifyOff)
    -- `GODEBUG` `fips140` off (`crypto/sha1`, with which `bootstrap` computes the member ids)
    (Hfips : crypto.fips140.GodebugFips140Off)
    -- restartN's members' first-start contracts (`bootstrap` at a first start of `k₅` members in one
    -- process: no spec of `bootstrap` covers it yet, see the header)
    (Hprem₅ : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_restartN.bootPremises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₅) n ids₅
          ps₅ ctxs₅ boot₅)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcdProgDirs k₅)),
    Robustness.Robust [] [(etcdProgram k₅, σ)] g
      (threads := 2 ^ 28) (bound := 2 ^ 48)

end adequacy
end EtcdGrove
end Perennial

end
