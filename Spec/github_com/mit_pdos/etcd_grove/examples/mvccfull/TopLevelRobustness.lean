/- Lean-first (no Rocq counterpart).

# `mvccfull`: the top-level robustness result, stated

`mvccfull_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/mvccfull/TopLevelRobustness.lean`.
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.TopLevelDefs
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI

section adequacy

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

variable [go_gctx : GoGlobalContext]

/-- **`mvccfull_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes, a fresh Go
process (`Robust`'s premise): in every execution of fewer than `mvccfullSteps` (`2 ^ 48`) steps along
which fewer than `mvccfullThreads` (`2 ^ 28`) threads are live, no thread is stuck and none has an
unrecovered panic, so none of the tester's checks fails.

**The program** (`mvccfullProgram r`, `TopLevelDefs.lean`): `mvccfull`'s initialization, then
`MainAt(r)`, which returns at once unless the directory `r` fits (`dirFits`) and nothing is at any
of the run's file paths, and otherwise runs `Run(MainConfig(r + "/mvccfull"))`.

**What it covers: one configuration, `MainConfig`** (`examples/mvccfull/config.go`), not every
`Config`. Its sizes: 12000 log operations, the keys of length 1 to 4 over `a`, `b`, `c`, values up to
5000 bytes, 2 readers and 2 watch streams per member, 4000 reads per reader and 64 watchers on a
member's streams between two restarts, the backend's batch limit 3, the store's compaction batch
limit 2. Its
`Mix`: every alternative of positive weight is among the executions; of the four of weight 0, three
pick from values another alternative also picks (`CompactAt`'s current revision, `RangeRev`'s and
`Start`'s compaction revision) and exclude nothing; the fourth, the readers' **corruption-checker
hashes** (`Read`'s last: `HashByRev`, `Hashes`), is excluded, and so is `Run`'s final `hashes()`
(`hashing(Mix.Read)` is false).

**The bounds.** `mvccfullThreads`: a cap the proof needs (the backend's reader-slot pool and the
stores' reader tokens are sized for `2 ^ 28` threads), not a limit of the code. `mvccfullSteps`: the
proof's cap, the run's receipt budget (`n` steps take `n + 1` receipts).

**The premises.** The package assumptions of the translations (`mvccfull`'s, the server's, the
cache's) and the `os` structs' field layouts, trusted; `HEnv`: `ETCD_VERIFY` off (an environment
fact); the file system at start (`Hfs`, `Fs.FsInit`) with `r` one of its roots (`Hr`). The extensions
are the etcd examples' (`etcdFsExts`), with no file I/O error (`etcdFsNoErr`). -/
def mvccfull_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [os.file.FieldAssumptions]
    [os.fileStat.FieldAssumptions] (r : GoString)
    (HEnv : EtcdVerifyOff)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (j0 : Fs.Ino)
    (Hr : (r, j0) ∈ (extLocal Fs.fsExt σ.world).fs.roots),
    Robustness.Robust [] [(mvccfullProgram r, σ)] g (threads := mvccfullThreads)
      (bound := mvccfullSteps)

end adequacy
end EtcdGrove
end Perennial

end
