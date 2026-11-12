/-
`(*wal.WAL).ReadAll` (WAL W4a, 2026-11-11, revised after the Freeze review; the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
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

/-- **`w.ReadAll()`** (S/wal.go:504-686, with F-Z and F-N4): from the newest valid snapshot `s`, the
relaxed read (`walReadCut` of the history at the read position). On success the WAL appends: the
read is fdatasynced, the zeroed tail included (F-Z), and the WAL directory and its parent are
fsynced (F-N4), so the history is synced (`walSyncedLb`, the mark at its length) and, with the area
`r` durable, the WAL's name is durable (`walNamed`); the records before `walReleasePos` are in
unlocked files (as `ReleaseLockTo`'s); the purge's right is given. An error leaves `w` failed
(`walReadFailed`): only `Close` accepts it (Go keeps the decoder, and a second `ReadAll` would read on
from the failure; etcd closes the handle and reopens, `bootstrap`, `renameWALUnlock`), and the state
as it was. -/
abbrev wal.WAL.ReadAll.spec : Prop :=
  ∀ (w : Loc) (r dir : GoString) (d : WalDur) (s : w64 × w64), walAreaDir r dir →
  some s = walNewestPair (walValidSnaps (d.H.map WalOpG.toM) d.cut) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpening w dir s ∗ walDiskAt dir d ∗ dirDurable r }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"ReadAll")) (Val #()))
  {{ (mdp : GoSlice) (hp : Loc) (sl : GoSlice) (err : GoInterface),
      RET (PairV (PairV (PairV #mdp #hp) #sl) #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ walReadFailed w dir ∗ walDiskAt dir d) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (σ : StorContents) (esL : List Loc),
        ⌜walReadCut (d.H.map WalOpG.toM) d.cut = some σ⌝ ∗ hsOpt hp σ.hs ∗ sl ↦*□ esL ∗
        walSaveEnts false esL σ.ents ∗ mdp ↦*□ d.metadata ∗ walOpenW w dir ∗
        walDiskAt dir { { d with m := max d.m d.H.length } with
          unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) s.1), named := true } ∗
        walNamed dir ∗ walSyncedLb dir d.H.length ∗ walLenLb w dir d.H.length ∗ walPurgeRight dir) }}

end spec

end EtcdGrove
end Perennial
