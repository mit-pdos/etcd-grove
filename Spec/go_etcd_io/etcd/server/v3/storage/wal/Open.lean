/-
`wal.Open` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds, and in W4a.1 and its revision 1 (2026-11-12, findings F-W4b-1/F-W4b-2 and the delta review's B1/M1/M2, decided by etcd-grove-81), and in W4a.2 (2026-11-12: the purge bounds' completeness, R1/R2, the soundness findings F-W4a2-1/F-W4a2-2, logically atomic restatements, decided by etcd-grove-81; the fork fixes `1aaca041c` and `0b50f0426` approved by the user; revision 1 after the Freeze review: no index `2^64-1` in `Save`/`SaveSnapshot`, decided by etcd-grove-81) the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `0b50f0426` (S/ = `server/storage/wal/`, line numbers of `c90b03b56`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.raft.v3.InvPbLog
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- **`Open(lg, dir, snap)`** (S/wal.go:377-379, write mode): opens the WAL at the snapshot `s`, locking
its files from the last one named `≤ s.1` on (`searchIndex`, `openAtIndex`, S/wal.go:395-466) and
leaving the earlier ones unlocked: `unl` is raised to `walOpenPos H s.1`, a position at or after the
start of the file `Open` locks from: the smaller of the guard's position (`walGuardPos`: the
snapshot record's last position under `walRelGuard`, 0 at index 0, else `|H|`) and the name bound
(the last position a file named at most `s.1` can start at, `walNameBound … false`; WAL W4a.2, R1:
`Open` locks from a file named exactly `s.1`, where `ReleaseLockTo` would not, so the two bounds
differ) (the step `"WalUnlock"` of that position, `wp_WalOpenHandle`; revision round 3, F1: the purge
right in the handle is then backed by a current `unl`). The name bound rests on a cut naming its
file `max(w.enti, w.snapi) + 1` (the fork's `0b50f0426`) and that maximum being at least `walLastIdx`
of the prefix (the larger of its last entry's index and its highest snapshot index) at every cut,
across restarts: true because a successful write-mode `ReadAll` matched its start record (the fork's
`1aaca041c`; finding F-W4a2-2: before it, an unmatched restart left `w.enti` low, and the landed
guard argument failed too, Go test `w4a2-tests` `TestW4a2UnmatchedRestartUnlocksGuardedRecord` at
`c90b03b56`; with `1aaca041c` alone, a raft-like restart failed, the fork's
`TestRestartAtSnapshotSavedBeforeReSentEntries`, which `0b50f0426` makes succeed) and no index wraps
(finding F-W4a2-1, `TestW4a2NameWrapUnlocksGuardedRecord`: ruled out at the source by `Save`'s and
`SaveSnapshot`'s premises, WAL W4a.2 revision 1; guard clause 4, `walHasMaxIdx`, and the `|H|`
fallbacks, now unreachable, are kept as a defense). Go tests `rev3-tests`:
`TestRev3PurgeWhileOpening` (the `|H|` branch) and `TestReview4OpenGuardPurge` (the guard branch);
the W4a.2 probe (every restart's `Open` of the WAL tester, the first locked file at or below
`walOpenPos`).
Nothing durable changes (read-only: its entry need not be durable). It takes the generation's lock
token (`walUnlockedTok`): the new handle carries it, and an error gives it back. So no `Open` is
provable while another handle exists, even one the program dropped without `Close` (Go releases
such a handle's locks by `os.File` finalizers and loses its buffered records: `Open` then succeeds
and `ReadAll` misses them, Go test `rev3-tests` `TestRev3LeakedHandleThenOpen`; revision round 3,
B2); in Go, `Open` next to a live handle fails (`TryLockFile`; `rev2-tests`
`TestRev2OpenWhileLocked`). With no WAL at `dir` (`o = none`) it fails (`readWALNames`). At a
snapshot with no record, the open succeeds and `ReadAll` is what must fail (its premise, and the
fork's fix). Logically atomic (WAL W4a.2, the W4c gate of W4a.1 revision 1, M-R1): W4c's restart runs under the
crash model, so the tester keeps the WAL in an invariant and finds it there at a crash during the
call; the post's `Q` is of the accessed state. The body commits at its locking (the step `"WalUnlock"` with the
handle, `wp_WalOpenHandle`; `WalBodies.walOpen_commit`); an error commits the same raise (the locks
may be taken before `OpenDir` fails, and a raise only allows more purging, which needs a handle). -/
abbrev wal.Open.spec : Prop :=
  ∀ (lg : Loc) (r dir : GoString) (sp : Loc) (s : w64 × w64) (Q : Option WalDur → IProp GF), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ walAreaOk r ∗ walSnapIdTerm sp s ∗ walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, walDirIs dir o }> @ ⊤, ∅
        <{ walDirIs dir (o.map (fun d => { d with unl := max d.unl (walOpenPos (d.H.map WalOpG.toM) s.1) })), COMM Q o }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Open)) (Val #lg)) (Val #dir)) (Val #sp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err); ∃ o : Option WalDur, Q o ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ walUnlockedTok) ∨
       (⌜err = GoInterface.nil⌝ ∗ ⌜o ≠ none⌝ ∗ walOpening w dir s)) }}

end spec

end EtcdGrove
end Perennial
