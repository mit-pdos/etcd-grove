/-
`(*wal.WAL).ReadAll` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds, and in W4a.1 and its revision 1 (2026-11-12, findings F-W4b-1/F-W4b-2 and the delta review's B1/M1/M2, decided by etcd-grove-81), and in W4a.2 (2026-11-12: the purge bounds' completeness, R1/R2, the soundness findings F-W4a2-1/F-W4a2-2, logically atomic restatements, decided by etcd-grove-81; the fork fixes `1aaca041c` and `0b50f0426` approved by the user) the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `0b50f0426` (line numbers of `c90b03b56`) (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.raft.v3.InvPbLog
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi

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

/-- **`w.ReadAll()`** (S/wal.go:504-686, with F-Z, F-N4 and the fork's `1aaca041c` and `0b50f0426`): from the newest
valid snapshot `s`, the relaxed read (`walReadCut` of the history at the read position). On success
the WAL appends: the read is fdatasynced, the zeroed tail included (F-Z), and the WAL directory and
its parent are fsynced (F-N4), so the history is synced (`walSyncedLb`, the mark at its length) and,
with the area `r` durable, the WAL's name is durable (`walNamed`); it unlocks nothing (`unl` is as
`Open` raised it, to `walOpenPos`; the landed text restated that raise, which a body committing at
the read cannot perform with the same step); the handle's purge right is
given (`walPurgeW`): the only way to it from an opened handle, since `walOpening` and
`walReadFailed` are sealed (revision round 3, F1). A write-mode `ReadAll` that matched no record of
`s` in the files `Open` selected returns `ErrSnapshotNotFound` (the fork's fix `1aaca041c`; WAL
W4a.2, finding F-W4a2-2: before it, the error was lost, and with the premise below holding, the files
`Open` selected could start after `s`'s record, VSE listing every record of the directory, so the
read returned less than `walReadCut`; Go test `w4a2-tests`
`TestW4a2UnmatchedRestartUnlocksGuardedRecord` at `c90b03b56`; nonissue
`etcd-wal-readall-snapshot-not-found-masked`, corrected). The fork's `0b50f0426` names every file
above every snapshot record before it, so `Open` at a snapshot of the history starts at or before its
record and the error arm is not reached that way (the fork's `TestReadAllStartRecordBeforeOpenedFile`
and `TestRestartAtSnapshotSavedBeforeReSentEntries`; the spec does not rely on it). So on success the read matched, and the premise `s = walNewestPair …` makes it the
read of the whole history from the read position. An error leaves `w` failed (`walReadFailed`):
only `Close` accepts it (Go keeps the decoder, and a second `ReadAll` would read on from the
failure; etcd closes the handle and reopens, `bootstrap`, `renameWALUnlock`). Logically atomic (WAL W4a.2, the W4c gate of W4a.1 revision 1, M-R1): W4c's restart runs under the
crash model, so the tester keeps the WAL in an invariant and finds it there at a crash during the
call; the post's `Q` is of the accessed state. The
premise is in the atomic precondition. The body commits at its read (the step `"WalNamed"` with the
handle, `wp_WalNamedOpen`, which turns it into an appending one, the accessed state weakened back:
the mark and `named` are lower bounds); then `"WalSync"` of `|H|` from the handle's length fact
(`wp_WalSyncLen`); `WalBodies.walReadAll_commit`. By the review checklist, `walSyncedLb dir |H|` and
`walNamed` bound only the mark and `named`, which the committed `walDiskAt` holds as lower bounds. -/
abbrev wal.WAL.ReadAll.spec : Prop :=
  ∀ (w : Loc) (r dir : GoString) (s : w64 × w64) (Q : WalDur → IProp GF), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpening w dir s ∗ dirDurable r ∗
      AU <{ ∃∃ d : WalDur, walDiskAt dir d ∗ ⌜some s = walNewestPair (walValidSnaps (d.H.map WalOpG.toM) d.cut)⌝ }> @ ⊤, ∅ <{ walDiskAt dir d, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"ReadAll")) (Val #()))
  {{ (mdp : GoSlice) (hp : Loc) (sl : GoSlice) (err : GoInterface),
      RET (PairV (PairV (PairV #mdp #hp) #sl) #err); ∃ d : WalDur, Q d ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ walReadFailed w dir) ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (σ : StorContents) (esL : List Loc),
        ⌜walReadCut (d.H.map WalOpG.toM) d.cut = some σ⌝ ∗ hsOpt hp σ.hs ∗ sl ↦*□ esL ∗
        walSaveEnts false esL σ.ents ∗ mdp ↦*□ d.metadata ∗ walOpenW w dir ∗
        walNamed dir ∗ walSyncedLb dir d.H.length ∗ walLenLb w dir d.H.length ∗ walPurgeW w dir)) }}

end spec

end EtcdGrove
end Perennial
