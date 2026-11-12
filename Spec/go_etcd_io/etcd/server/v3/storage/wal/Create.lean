/-
`wal.Create` (WAL W4a, 2026-11-11, revised after the Freeze review; the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
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

/-- **`Create(lg, dir, md)`** (S/wal.go:102-262, with F-N1): a fresh WAL with metadata `md` in `dir`
(`dir = r/n`, a WAL directory of the area `r`, which is durable). The atomic update commits at
the rename of `dir.tmp` onto `dir` (`walDurFresh md`: no record past `Create`'s own, which the
reader ignores); `dir.tmp`'s first segment and entry are synced before it (F-N1), and the parent's
fsync after it makes `dir`'s entry durable (`walNamed`). An error before the rename leaves `dir`
untouched (the update not committed; `Exist`'s check failing to read `dir` is such an error,
`os.ErrExist`). After the rename, any error is an I/O failure (`¬ storage.walCreateOk`, the server's
environment premise): the WAL may stay at `dir` (`renameWAL`'s `OpenDir`, `renameWALUnlock`'s
`Open`/`ReadAll`, S/wal.go:340-367) or be renamed to `dir.broken.*` (`cleanupWAL`); the model claims
nothing then. The removals (`dir.tmp`, and `dir` when it holds no WAL) touch only
`walCreateRegion dir`, which under the area holds no other WAL, no durable directory and no durable
file. -/
abbrev wal.Create.spec : Prop :=
  ∀ (lg : Loc) (r dir : GoString) (mp : GoSlice) (md : List w8) (Q : IProp GF), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ mp ↦*□ md ∗ walAreaOk r ∗ dirDurable r ∗
      AU <{ walAbsent dir }> @ ⊤, ∅ <{ walDiskAt dir (walDurFresh md), COMM Q }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Create)) (Val #lg)) (Val #dir)) (Val #mp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      (⌜err = GoInterface.nil⌝ ∗ Q ∗ walOpenW w dir ∗ walNamed dir ∗ walLenLb w dir 0 ∗
        walSyncedLb dir 0 ∗ walPurgeRight dir) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗
        AU <{ walAbsent dir }> @ ⊤, ∅ <{ walDiskAt dir (walDurFresh md), COMM Q }>) ∨
      ⌜¬ storage.walCreateOk⌝ }}

end spec

end EtcdGrove
end Perennial
