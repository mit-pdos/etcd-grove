/-
`wal.Open` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds; the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
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
its files from the one holding `s` on (`searchIndex`, `openAtIndex`, S/wal.go:395-466) and leaving
the earlier ones unlocked: on success `unl` is raised to `walReleasePos H s.1`, a position at or after the start of the file `Open` locks from (the snapshot record's last position under `walRelGuard`, 0 at index 0, else `|H|`) (the step `"WalUnlock"` of that
position, `wp_WalOpenHandle`; revision round 3, F1: the purge right in the handle is then backed by a
current `unl`). Go tests `rev3-tests`: `TestRev3PurgeWhileOpening` (the `|H|` branch: a purge in the
window between `Open` and `ReadAll` deletes the unlocked file before the snapshot's) and
`TestReview4OpenGuardPurge` (the `walRelGuard` branch: the purge deletes only files before the
snapshot record's position).
Nothing durable changes (read-only: its entry need not be durable). It takes the generation's lock
token (`walUnlockedTok`): the new handle carries it, and an error gives it back. So no `Open` is
provable while another handle exists, even one the program dropped without `Close` (Go releases
such a handle's locks by `os.File` finalizers and loses its buffered records: `Open` then succeeds
and `ReadAll` misses them, Go test `rev3-tests` `TestRev3LeakedHandleThenOpen`; revision round 3,
B2); in Go, `Open` next to a live handle fails (`TryLockFile`; `rev2-tests`
`TestRev2OpenWhileLocked`). With no WAL at `dir` (`o = none`) it fails (`readWALNames`). At a
snapshot with no record, the open succeeds and `ReadAll` is what must fail (its premise). -/
abbrev wal.Open.spec : Prop :=
  ∀ (lg : Loc) (r dir : GoString) (o : Option WalDur) (sp : Loc) (s : w64 × w64), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ walAreaOk r ∗ walDirIs dir o ∗ walSnapIdTerm sp s ∗ walUnlockedTok }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Open)) (Val #lg)) (Val #dir)) (Val #sp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ walDirIs dir o ∗ walUnlockedTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ d : WalDur, ⌜o = some d⌝ ∗
        walDiskAt dir { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) s.1) } ∗
        walOpening w dir s) }}

end spec

end EtcdGrove
end Perennial
