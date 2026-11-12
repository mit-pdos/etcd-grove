/-
`wal.ValidSnapshotEntries` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds, and in W4a.1 and its revision 1 (2026-11-12, findings F-W4b-1/F-W4b-2 and the delta review's B1/M1/M2, decided by etcd-grove-81); the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
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

/-- **`ValidSnapshotEntries(lg, dir)`** (S/wal.go:688-775): decodes every remaining file read-only; its
result is the snapshot records from the read position on at or below the history's last commit
(`walValidSnaps`), or an error. The read position `cut` is the first remaining file's start: a crash
or a purge round moves it. With no WAL at `dir` (`o = none`: no `.wal` file, or no directory) it
fails (`readWALNames`). The caller holds the generation's lock token (`walUnlockedTok`; W4a.1,
2026-11-12, finding F-W4b-2), so the whole history is in the files: with the token, every handle of
this generation that wrote was closed successfully (`Close` flushes and fdatasyncs before it gives
the token back; only `Close` returns a token that a handle took), and a handle left by a failed
`Open` may still hold locks but wrote nothing; a handle dropped without `Close` took the token with
it; the previous generation's records are the crash's image itself, which the files hold, unsynced
records included (a torn record at the end is `ErrUnexpectedEOF`, which it tolerates). Go tests
`w4a1-tests`: `TestW4a1VSEFullAfterClose`, `TestW4a1VSEKillImage` (a kill image holding unsynced
commit records: VSE reads them, so a snapshot record they validate is returned) and
`TestW4a1VSEDroppedHandle` (a handle dropped to finalizers loses its buffered records and VSE reads a
prefix: the token, gone with the handle, is what keeps the triple from applying). Logically atomic
(revision 1, the delta review's M2: the tester's invariant holds `walDirIs`): with the token held no
other call moves the state (a write needs a handle, so the token; `Repair` and `Exist` move
nothing), so the body linearizes at any point of its read; its result is a function of the
accessed state, argued logically (the steps model writes; a read returns nothing). Revision 1
dropped W4a's token-free triple (a prefix `H.take j`, `j ≥ m`, for a caller with a live append
handle, whose encoder buffers records; Go tests `rev2-tests` `TestRev2VSELiveUnflushed`,
`TestRev2VSELiveLargeBuffered`): neither the tester (W4c) nor etcd's bootstrap (C6) calls VSE with a
live handle, and a plain triple would not compose with W4c's invariant. -/
abbrev wal.ValidSnapshotEntries.spec : Prop :=
  ∀ (lg : Loc) (r dir : GoString) (Q : Option WalDur → IProp GF), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ walAreaOk r ∗ walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, walDirIs dir o }> @ ⊤, ∅ <{ walDirIs dir o, COMM Q o }> }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries)) (Val #lg)) (Val #dir))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); walUnlockedTok ∗ ∃ o : Option WalDur, Q o ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ∃ (d : WalDur) (ps : List Loc), ⌜o = some d⌝ ∗ sl ↦*□ ps ∗
        walSnapsAt ps (walValidSnaps (d.H.map WalOpG.toM) d.cut)) }}

end spec

end EtcdGrove
end Perennial
