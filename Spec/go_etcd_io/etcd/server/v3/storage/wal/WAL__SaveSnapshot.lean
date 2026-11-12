/-
`(*wal.WAL).SaveSnapshot` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds, and in W4a.1 and its revision 1 (2026-11-12, findings F-W4b-1/F-W4b-2 and the delta review's B1/M1/M2, decided by etcd-grove-81); the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
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
written; always fdatasynced. An error is an I/O failure (`¬ storage.walSaveOk`). Stated over
`walDiskAt` (W4a.1, 2026-11-12, finding F-W4b-1; revision 1), as `Save`: the update moves the history
only (a cut, S/wal.go:864-938, unlocks nothing and rewrites the same metadata; Go test `w4a1-tests`
`TestW4a1SaveKeepsPurgePositions`); the body (`WalBodies.walSaveSnapshot_body`) commits at
`"WalAppend"`, then performs `"WalSync"` of the new length from its handle's fact alone. -/
abbrev wal.WAL.SaveSnapshot.spec : Prop :=
  ∀ (w : Loc) (dir : GoString) (sp : Loc) (md : SnapshotMetadataM) (cs : Bool) (sized : Bool)
    (Q : WalDur → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpenW w dir ∗ walSnapAt sp md cs ∗
      ⌜md.Index' = W64 0 ∨ cs = true⌝ ∗
      AU <{ ∃∃ d : WalDur, walDiskAt dir d ∗ ⌜d.sized = sized⌝ }> @ ⊤, ∅
        <{ walDiskAt dir { d with H := d.H ++ [WalOpG.snap md] }, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"SaveSnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err; walOpenW w dir ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ d : WalDur, Q d ∗ walLenLb w dir (d.H.length + 1) ∗
          walSyncedLb dir (d.H.length + 1)) ∨
       ⌜¬ storage.walSaveOk⌝) }}

end spec

end EtcdGrove
end Perennial
