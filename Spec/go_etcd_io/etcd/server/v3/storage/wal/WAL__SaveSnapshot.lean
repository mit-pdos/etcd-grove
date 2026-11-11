/-
`(*wal.WAL).SaveSnapshot` (WAL W4a, 2026-11-11; the approved W4 Draft's §1.4, `notes/decisions.md`, "WAL W4a") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `b18c2d500` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
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

/-- **`w.SaveSnapshot(e)`** (S/wal.go:1119-1164): one snapshot record of `e`'s index and term (its conf
state, D6, non-nil unless the index is 0: `ValidateSnapshotForWrite`), committed before the record is
written; always fdatasynced. An error is an I/O failure (`¬ storage.walSaveOk`). -/
abbrev wal.WAL.SaveSnapshot.spec : Prop :=
  ∀ (w : Loc) (dir : GoString) (sp : Loc) (md : SnapshotMetadataM) (cs : Bool) (sized : Bool)
    (Q : WalHist → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpenW w dir ∗ walSnapAt sp md cs ∗
      ⌜md.Index' = W64 0 ∨ cs = true⌝ ∗
      AU <{ ∃∃ H : WalHist, walDisk dir H sized }> @ ⊤, ∅
        <{ walDisk dir (H ++ [WalOpG.snap md]) sized, COMM Q H }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"SaveSnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err; walOpenW w dir ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ H : WalHist, Q H ∗ walLenLb w (H.length + 1) ∗
          walSyncedLb dir (H.length + 1)) ∨
       ⌜¬ storage.walSaveOk⌝) }}

end spec

end EtcdGrove
end Perennial
