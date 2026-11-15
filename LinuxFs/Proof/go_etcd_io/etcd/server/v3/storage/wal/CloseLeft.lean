/-
**What a failed `Close` of a failed read leaves** (unit `locks`, session 3; ledger 2026-11-15, "`WAL.Close.specFailed`'s
error arm for the boot path's `Repair`", P7 continued). `(*wal.WAL).Close()` returns `w.sync()`'s error before it
closes any lock (S/wal.go:1060-1066): the locks stay held, the handle's ghost (the lock token) cannot be put back,
and what the handle held of the WAL directory stays the caller's. `walCloseLeft R dir` is that: the shared
invariant of the roots `R` and a path to `dir` (its inode `j`), the handle's half of the directory's claim
(`osNames j (.except X)`, the names `X` it leaves out not `.wal` names), with the layout's facts about its names
(the named segments `segs`, in name order, each a `walFileName`, the last `gL`), the last segment's lock (held
through the tail's description, of `fileutil`'s kind), and the call permission's half the handle and its pipeline
held. Exactly what `wal.Repair.specHeld` takes but the client's half of the call permission: so the boot path
(`openWALFromSnapshot`: a failed `ReadAll`, `w.Close()` ignored, `Repair`) composes
(`CloseFailedRepair.lean`). Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenLastDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a failed `Close` of a failed read leaves** (see the file header). -/
def walCloseLeft (dir : GoString) : IProp GF :=
  iprop(∃ (R : Roots) (j : Ino) (X : List GoString) (hj : NamesH) (segs : List SegG) (gL : SegG) (qd : Qp)
      (k : LockKind) (fd : w64),
    ⌜CloseLeftOk X hj segs gL⌝ ∗ osSharedInv R ∗ osPathS R dir (DFrac.own qd) j ∗
    osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    osLock k gL.ino fd ∗ fileutil.lockKind k ∗ osCallPerm (1 : Qp).half)

end defs

end WalFs
end EtcdGrove
end Perennial
