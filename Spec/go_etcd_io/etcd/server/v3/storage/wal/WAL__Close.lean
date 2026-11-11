/-
`(*wal.WAL).Close` (WAL W4a, 2026-11-11; the approved W4 Draft's §1.4, `notes/decisions.md`, "WAL W4a") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `b18c2d500` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
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

/-- **`w.Close()`** (S/wal.go:1028-1052). Of a WAL opened to append: syncs every record, closes and
unlocks its files; the purge's right is consumed (the purge must have stopped, as `walPurgeRight`
says). An error is an I/O failure (`¬ storage.walCloseOk`). Of a WAL opened for reading (after a
failed `ReadAll`): nothing the model tracks changes. -/
abbrev wal.WAL.Close.spec : Prop :=
  (∀ (w : Loc) (dir : GoString) (H : WalHist) (sized : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpenW w dir ∗ walDisk dir H sized ∗ walPurgeRight dir }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; walDisk dir H sized ∗
        ((⌜err = GoInterface.nil⌝ ∗ walSyncedLb dir H.length) ∨ ⌜¬ storage.walCloseOk⌝) }}) ∧
  (∀ (w : Loc) (dir : GoString) (s : w64 × w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpening w dir s }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; True }})

end spec

end EtcdGrove
end Perennial
