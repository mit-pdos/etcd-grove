/-
`(*wal.WAL).Close()` as `Create`'s `cleanupWAL` calls it (S/wal.go:1053-1077; W4 of
`notes/wal-fsext-plan.md`, twenty-fifth session; ledger 2026-11-14): `WAL.Close.spec` over the handle
before naming (`walOpenWFU`), with no client update (after the commit the client holds `walDiskAt`).
Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

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
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **`w.Close()` of the handle before naming** (`Create`'s cleanup): `WAL.Close.spec`'s effects
(the pipeline closed, the tail synced, every lock's file and the directory's closed, the purge right
consumed) with nothing committed: the free lock token back (`walUnlockedTok`, `walCloseLawU`) with the whole
call permission, whatever `err` (the directory's `Close` may fail after everything else), or, the sync
failed (`Close` returns before it unlocks), the lock token still held (`walLockedTok`: `WAL.sync.specC`'s
error arm), which `Create` needs to merge `nm.tmp`'s claim back to the area. The `dir` field comes back
with the free token (`cleanupWAL` reads `w.dir` after `Close`, for the rename). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specU (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWFU P Mr w dir ∗ WalFs.walPurgeW w dir }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗ WalFs.walUnlockedTok ∗
        osCallPerm 1) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walLockedTok) }}

end spec

end EtcdGrove
end Perennial
