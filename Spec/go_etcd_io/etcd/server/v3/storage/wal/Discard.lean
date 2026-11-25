/-
`wal.Discard` over `fsExt` (P6b, mit-pdos/etcd-grove#50; fork `goose-lean-fmt1c-discardfix` @ `251a430ce`,
`server/storage/wal/unsaved.go:93`): `RemoveAll(dir.tmp)`, `Rename(dir, dir.tmp)`, `syncDir(Dir(dir))`, then a log
line. Ledger `notes/specs-only/ledger.md`, 2026-11-25, "wal.Discard". Proved in
`Proof/go_etcd_io/etcd/server/v3/storage/wal/Discard.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`Discard(lg, dir)`** (unsaved.go:93-116): removes `dir.tmp` (`os.RemoveAll`), renames the WAL's
directory onto it (`os.Rename(dir, dir.tmp)`) and fsyncs the parent (`syncDir(filepath.Dir(dir))`), so that a
WAL whose first `Save` never completed goes away atomically across a crash; it does not read the WAL (the
caller found it unsaved with `Unsaved` and removed the backend first: `bootstrap.go:91-101`).

Two updates, since the client's view changes twice (ledger 2026-11-25, "wal.DiscardUnsaved" and "wal.Discard"):
* `AU₁`, at the rename's commit: the WAL at `dir`, incarnation `ic`, becomes **unnamed** at incarnation
  `ic + 1` (between the rename and the fsync a crash may keep it or lose it, so every `walNamed dir ic` is
  retired);
* `AU₂`, at the parent's fsync: no WAL at `dir`, incarnation `ic + 2` (a re-`Create`'s facts are of a new
  incarnation).

The caller holds the lock token (`walUnlockedTok`: no handle open) and the area's resources, as `Create`;
`RemoveAll` and `Rename` cannot fail under the premise (`FsNoErrOn` on `dir`, `dir.tmp`, the area), only the
fsync can. Post: `nil` with both results, the token and `walAreaRes` back (the area's claim now covers the old
WAL's name); an error (the fsync failed) with `AU₁`'s result and `AU₂` unconsumed, the token and `walAreaRes`
lost (the WAL left unnamed at `dir.tmp`, as `Create`'s failed arm leaves its WAL). -/
abbrev wal.Discard.spec (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp) (ic : Nat)
    (Q₁ : WalDur → IProp GF) (Q₂ : IProp GF),
  InArea r dir nm → NameOk nm → dir.length < 2 ^ 59 → cleanAbsPath r →
  FsNoErrOn (fun p => p = dir ∨ p = dir ++ go!".tmp" ∨ p = r) ∧ PathFits (dir ++ go!".tmp") ∧ PathFits dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ WalFs.dirDurable r ∗ osPathS R r (DFrac.own qp) jr ∗
      walAreaRes jr ∗ osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir ic d }> @ walAuMask, ∅
        <{ WalFs.walDiskAtI dir (ic + 1) { d with named := false }, COMM Q₁ d }> ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir (ic + 1) d }> @ walAuMask, ∅
        <{ WalFs.walAbsentI dir (ic + 2), COMM Q₂ }> }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Discard)) (Val #lg)) (Val #dir))
  {{ (err : GoInterface), RET #err;
      osPathS R r (DFrac.own qp) jr ∗ osCallPerm (callKey R r) 1 ∗ (∃ d : WalDur, Q₁ d) ∗
      ((⌜err = interface.nil⌝ ∗ walAreaRes jr ∗ WalFs.walUnlockedTok ∗ Q₂) ∨
        (⌜err ≠ interface.nil⌝ ∗
          AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir (ic + 1) d }> @ walAuMask, ∅
            <{ WalFs.walAbsentI dir (ic + 2), COMM Q₂ }>)) }}

end spec

end EtcdGrove
end Perennial
