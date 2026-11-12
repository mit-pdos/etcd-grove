/-
`purgeRound` of the WAL robustness tester (`examples/etcd/wal`, WAL W4c; the decision Q2 of the W4c
plan, etcd-grove-81, 2026-11-12). Names-only (`Code/.../examples/etcd/wal.toml`): an axiom at the
trust boundary (`Proof/.../examples/etcd/wal/purgeRound.lean`), true of its Go body (one round of
fileutil.purgeFile's loop, `examples/etcd/wal/wal.go`) over the WAL at the etcd pin `0b50f0426`
(S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`. Its
body is read as one that performs the abstract-disk extension's step `"WalPurge"` of the position it
deleted up to (`Proof/.../examples/etcd/wal/PurgeBody.lean`, proved). Go evidence:
`examples/etcd/wal/purge_test.go`, and the WAL tester under the crash harness (`notes/decisions.md`,
"WAL W4c").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.wal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- **`purgeRound(lg, dir, keep)`** (`examples/etcd/wal/wal.go`), while `w` is the WAL open in `dir`
with its purge right: one round of `fileutil.purgeFile`'s loop (client/pkg/fileutil/purge.go), as
the server's WAL purge runs it (suffix `"wal"`). It lists `dir` (`fileutil.ReadDir`, sorted by
name), keeps the names ending in `"wal"`, and, oldest first, for each but the newest `keep`: takes
its lock (`TryLockFile`, non-blocking), removes the file and releases the lock; it stops at the
first file whose lock it cannot take or that it cannot remove (and does nothing on a `ReadDir`
error). No directory fsync.

Atomic update: `pur` raised to `unl`, the read position `cut` moved to some `k` with
`cut ≤ k ≤ max pur unl` (the extension's `"WalPurge"` step), which is the start of the first file
the round left. Why that is what Go does:
* A WAL file is named `seq-index.wal` with `%016x` fields (S/util.go `walName`), and the sequence
  numbers grow with the position, so name order is history order; the WAL directory holds no other
  name ending in `"wal"` (the pipeline's `N.tmp`, Repair's `.broken` copies end otherwise; `Create`
  builds in `dir.tmp`, outside `dir`). So the round deletes a prefix of the files: `k ≥ cut`.
* While `w` is open, its files from the one holding position `unl` on are locked by `w` (`unl`'s
  meaning: `Open`, `ReleaseLockTo` and the tail's `LockFile` keep them locked; `walOpenW` and the
  generation's lock token say no other handle exists), and `TryLockFile` of a file another open
  file description holds fails (OFD or `flock` locks are per open file description, so the
  tester's own process conflicts with itself, as etcd's purge goroutine does with its WAL). So the
  round stops at or before that file: every deleted file holds only records before `unl`, and
  `k ≤ unl` when it deleted any; otherwise `k = cut ≤ pur`.
* Removes undone by a power loss (no directory fsync) and partial rounds only leave fewer files
  deleted: the crash relation (`walCrash`) lets the next read's purged prefix be any position up to
  `min pur |I|`, and the round raised `pur` before it removed anything (the commit is the round's
  first step; between it and the return no other thread can read `cut`: `w`'s token excludes
  every other `Open`).
* Raising `pur` to `unl` when the round deletes less (an error, a locked file, `keep`) only allows
  more: `pur` bounds what may be missing.

The precondition holds `walOpenW w dir` and `walPurgeW w dir` (the W4c gate of WAL W4a revision
round 3, M1): framed, never derived. Without an open handle Go's round deletes every file but the
newest `keep`, including those holding records at or after `unl` (Go test
`TestPurgeRoundNoHandle`), so a spec without them would be false. No other precondition: the round
touches only `dir`'s entries ending in `"wal"`, and never reads the tester's or `fileutil`'s package
variables but `fileutil`'s lock functions, which its initializer sets (no package-initialization
premise, as `fileutil.TouchDirAll.spec`: neither package is in `etc/gen-init.py`'s closure yet). The
post's `Q` is of the accessed state and the chosen position; the post gives no fact about a past
state. -/
abbrev purgeRound.spec : Prop :=
  ∀ (lg w : Loc) (dir : GoString) (keep : w64) (Q : WalDur → Nat → IProp GF),
  {{ walOpenW w dir ∗ walPurgeW w dir ∗
      AU <{ ∃∃ d : WalDur, walDiskAt dir d }> @ ⊤, ∅
        <{ ∀∀ k : Nat, ⌜d.cut ≤ k ∧ k ≤ max d.pur d.unl⌝ ∗
            walDiskAt dir { d with pur := max d.pur d.unl, cut := k }, COMM Q d k }> }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.purgeRound))
      (Val #lg)) (Val #dir)) (Val #keep))
  {{ RET #(); walOpenW w dir ∗ walPurgeW w dir ∗ ∃ d k, Q d k }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
