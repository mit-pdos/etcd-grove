/-
`wal.ValidSnapshotEntries` (WAL W4a, 2026-11-11; the approved W4 Draft's §1.4, `notes/decisions.md`, "WAL W4a") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `b18c2d500` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
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

/-- **`ValidSnapshotEntries(lg, dir)`** (S/wal.go:688-775): decodes every remaining file; its result is
the snapshot records from the read position on at or below the history's last commit
(`walValidSnaps`), or an error. -/
abbrev wal.ValidSnapshotEntries.spec : Prop :=
  ∀ (lg : Loc) (dir : GoString) (d : WalDur),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ walDiskAt dir d }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries)) (Val #lg)) (Val #dir))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); walDiskAt dir d ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ∃ ps : List Loc, sl ↦*□ ps ∗
        walSnapsAt ps (walValidSnaps (d.H.map WalOpG.toM) d.cut)) }}

end spec

end EtcdGrove
end Perennial
