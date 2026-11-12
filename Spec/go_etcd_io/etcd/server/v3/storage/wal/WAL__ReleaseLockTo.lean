/-
`(*wal.WAL).ReleaseLockTo` (WAL W4a, 2026-11-11, revised after the Freeze review; the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
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

/-- **`w.ReleaseLockTo(a)`** (S/wal.go:984-1026): unlocks the files before the one holding the last
record at or below `a`; with a synced snapshot record of index `a`, every record from
`walReleasePos` on stays in a locked file: the snapshot record's last position when every later cut
names its file above `a` (`walRelGuard`, which etcd's histories meet: raft's entries after a snapshot
are above it), else the history's length (`unl`). An error leaves the state as it was. -/
abbrev wal.WAL.ReleaseLockTo.spec : Prop :=
  ∀ (w : Loc) (dir : GoString) (d : WalDur) (a t : w64) (i n : Nat) (cs : ConfStateM),
  d.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩) → i < n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpenW w dir ∗ walDiskAt dir d ∗ walSyncedLb dir n }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"ReleaseLockTo")) (Val #a))
  {{ (err : GoInterface), RET #err; walOpenW w dir ∗
      ((⌜err = GoInterface.nil⌝ ∗ walDiskAt dir { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) a) }) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ walDiskAt dir d)) }}

end spec

end EtcdGrove
end Perennial
