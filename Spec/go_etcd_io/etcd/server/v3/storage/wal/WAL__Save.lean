/-
`(*wal.WAL).Save` (WAL W4a, 2026-11-11, revised after the Freeze review; the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
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

/-- **`w.Save(st, ents)`** (S/wal.go:1075-1117): no premise on the entries. The atomic update commits
before the call writes a record (a crash mid-call leaves an image of `H ++ [op]` past the mark,
`walImg`): the entries' records, then `st`'s unless it is empty (`saveState`). On success the WAL has
written the history up to its new length (`walLenLb`), and if the save must sync (`walMustSync`:
entries, or a changed vote or term) it has fdatasynced every record so far (`walSyncedLb`; also
when it cut, which syncs). An error is an I/O failure (`¬ storage.walSaveOk`). -/
abbrev wal.WAL.Save.spec : Prop :=
  ∀ (w : Loc) (dir : GoString) (hp : Loc) (hs : HardStateM) (sl : GoSlice) (esL : List Loc)
    (es : List EntryM) (sized : Bool) (Q : WalHist → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpenW w dir ∗ hsOpt hp hs ∗ sl ↦*□ esL ∗
      walSaveEnts sized esL es ∗
      AU <{ ∃∃ H : WalHist, walDisk dir H sized }> @ ⊤, ∅
        <{ walDisk dir (H ++ [WalOpG.save hs es]) sized, COMM Q H }> }}
    (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Save")) (Val #hp)) (Val #sl))
  {{ (err : GoInterface), RET #err; walOpenW w dir ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ H : WalHist, Q H ∗ walLenLb w dir (H.length + 1) ∗
          (⌜walMustSync H hs es⌝ -∗ walSyncedLb dir (H.length + 1))) ∨
       ⌜¬ storage.walSaveOk⌝) }}

end spec

end EtcdGrove
end Perennial
