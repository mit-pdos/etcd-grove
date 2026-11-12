/-
`(*wal.WAL).Close` (WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds, and in W4a.1 and its revision 1 (2026-11-12, findings F-W4b-1/F-W4b-2 and the delta review's B1/M1/M2, decided by etcd-grove-81); the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names (`Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` gives the bodies of the posts that name a past state). `walDiskAt`'s synced mark and `named` are lower bounds of the real ones (W4a.1 revision 1, `GooseLang/Ext/AbsDisk/Specs.lean`).
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
unlocks its files; the handle's purge right is consumed (`walPurgeW`: the purge must have stopped,
since `Close` unlocks every file). An error is an I/O failure (`¬ storage.walCloseOk`). Of a WAL opened for reading, or whose
`ReadAll` failed: nothing the model tracks changes (the handle and its purge right are consumed).
Either way, on success the generation's lock token is given back (`walUnlockedTok`, its step
`wp_WalCloseHandle`): `Close` released every lock, so the next `Open` or `Create` may succeed. On
an error it is not: `Close` returns at a failed `sync` before it unlocks (S/wal.go:1037-1040, the return at 1039), and a
failed `dirFile.Close` is an I/O failure too (`¬ storage.walCloseOk`, the server's environment
premise); the second conjunct's `Close` also syncs the tail, so it gained the same error arm. The
first conjunct is logically atomic (W4a.1 revision 1, the delta review's M2: a client keeps the WAL in
an invariant, so a crash during `Close` finds `walDiskAt` there, before or after the commit): the
body opens the update, performs `"WalSync"` of the history's length with the accessed `walDiskAt`
and commits it unchanged (the mark a lower bound; `WalBodies.walClose_commit`), then gives the token
back (`wp_WalCloseHandle`). Every field but the mark is kept (the metadata read back after a reopen,
Go test `w4a1-tests` `TestW4a1SaveKeepsPurgePositions`). -/
abbrev wal.WAL.Close.spec : Prop :=
  (∀ (w : Loc) (dir : GoString) (Q : WalDur → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walOpenW w dir ∗ walPurgeW w dir ∗
        AU <{ ∃∃ d : WalDur, walDiskAt dir d }> @ ⊤, ∅ <{ walDiskAt dir d, COMM Q d }> }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ ∃ d : WalDur, Q d ∗ walSyncedLb dir d.H.length ∗ walUnlockedTok) ∨
        ⌜¬ storage.walCloseOk⌝ }}) ∧
  (∀ (w : Loc) (dir : GoString) (s : w64 × w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ (walOpening w dir s ∨ walReadFailed w dir) }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; (⌜err = GoInterface.nil⌝ ∗ walUnlockedTok) ∨ ⌜¬ storage.walCloseOk⌝ }})

end spec

end EtcdGrove
end Perennial
