/-
`wal.ValidSnapshotEntries` (WAL W4a, 2026-11-11, revised after the Freeze review and its second round; the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
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
result is the snapshot records from the read position on at or below the last commit of a prefix
of the history (`walValidSnaps` of `H.take j`), or an error. The prefix: what reached the files,
which is every synced operation (`j ≥ m`) and, while an append handle is open, possibly less than
`H` (`Save` buffers its records in the encoder until a sync or a page fills; a torn record at the
end is `ErrUnexpectedEOF`, which it tolerates; a `Save`'s state record is written last, so a
partly flushed `Save` is a prefix too). Revision round 2, B1 (Go test `rev2-tests`
`TestRev2VSELiveUnflushed`, `TestRev2VSELiveLargeBuffered`); at a restart (etcd's use, bootstrap
before `Open`) `j = |H|` is the image. The read position `cut` is the first remaining file's start: a
crash or a purge round moves it. With no WAL at `dir` (`o = none`: no `.wal` file, or no directory)
it fails (`readWALNames`). -/
abbrev wal.ValidSnapshotEntries.spec : Prop :=
  ∀ (lg : Loc) (r dir : GoString) (o : Option WalDur), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ walAreaOk r ∗ walDirIs dir o }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries)) (Val #lg)) (Val #dir))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); walDirIs dir o ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ∃ (d : WalDur) (j : Nat) (ps : List Loc), ⌜o = some d⌝ ∗
        ⌜d.m ≤ j ∧ j ≤ d.H.length⌝ ∗ sl ↦*□ ps ∗
        walSnapsAt ps (walValidSnaps ((d.H.take j).map WalOpG.toM) d.cut)) }}

end spec

end EtcdGrove
end Perennial
