/-
`(*wal.WAL).Close()` as `Create`'s `cleanupWAL` calls it (S/wal.go:1053-1077; W4 of
`notes/wal-fsext-plan.md`, twenty-fifth session; ledger 2026-11-14): `WAL.Close.spec` over the handle
before naming (`walOpenWFU`), with no client update (after the commit the client holds `walDiskAt`).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

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
consumed) with nothing committed: the free lock token back but for its names fragment
(`walUnlockedTokX`, `walCloseLawU`), the handle's names fragment `some dir` (`Create`'s pending
registration), the handle's half of the call permission (its quarter and the pipeline's), and the two
pinned paths to `dir` (the handle's and the pipeline's, at the roots `Rp` and fraction `qp` `Create`
lent: with them `Create` has the program's half of the name's claim whole again for its cleanup's
rename; design P, `notes/wal-units/create.md`), whatever `err` (the directory's `Close` may fail after
everything else); or, the sync failed (`Close` returns before it unlocks), the lock token still held
(`walLockedTok`: `WAL.sync.specC`'s error arm), which `Create` needs to merge `nm.tmp`'s claim back to the
area, with the names fragment (`Create` then registers the name, which still holds the WAL). The `dir`
field comes back with the free token (`cleanupWAL` reads `w.dir` after `Close`, for the rename). And the
tail's `*os.File` (pinned to `tf`, `Create`'s segment file): closed (fd `-1`) after a successful sync, open
with its fd when the sync failed (`Close` returned before closing the locks); `Create`'s deferred
`f.Close()` runs on it. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specU (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (Rp : Roots) (qp : Qp) (tf : Loc),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWFU P Mr w dir Rp qp tf ∗ WalFs.walPurgeW w dir }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗ WalFs.walUnlockedTokX ∗
        WalFs.walNamesFrag (some dir) ∗ osCallPerm (1 : Qp).half ∗
        (∃ j : Ino, osPathS Rp dir (DFrac.own qp) j ∗ osPathS Rp dir (DFrac.own qp) j) ∗
        ∃ nmf : GoString, os.ownFile tf (-1 : w64) nmf (DFrac.own 1)) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walLockedTok ∗ WalFs.walNamesFrag (some dir) ∗
        ∃ (fd : w64) (nmf : GoString) (d : OsFd),
          os.ownFile tf fd nmf (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d ∗ fdLocks fd d) }}

end spec

end EtcdGrove
end Perennial
