/-
`(*wal.WAL).SaveSnapshot` with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`):
`SaveSnapshot.spec` over a semantics whose steps satisfy **no I/O error on chosen files** (`FsStepSat
(NoIoErr Sio)`, `GooseLang/Ext/Fs/Premises.lean`), with the coverage the user chose for now (2026-11-15,
coverage (a), `notes/decisions.md`, "fsExt: no I/O errors on chosen files"): every file of the roots'
trees (etcd's data directory), `∀ st i, Sio.ino st i`. etcd's server panics when the apply thread's
`SaveSnap` fails (`notes/wal-units/specgap.md` P1). Proved in
`LinuxFs/Proof/.../wal/WAL__SaveSnapshotNoErr.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshot
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleRoom
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`w.SaveSnapshot(e)` with no I/O error** (see the file header): `SaveSnapshot.spec`'s success arm,
`nil` returned, of a handle whose tail has room for the record's frame and `k` more (`walOpenWFR … (k +
|encSnap md| + 64)`: the frame is at most the data plus 64 bytes, and a write reaching ext4's `s_maxbytes`
fails with `EFBIG`, which the premise does not exclude); the handle comes back with room `k`. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.specNoErr (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (sp : Loc)
    (md : SnapshotMetadataM) (cs : Bool) (sized : Bool) (Q : WalDur → IProp GF) (k : Nat),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ WalFs.walOpenWFR P Mr w dir (k + (Mr.encSnap md).length + 64) ∗
      walSnapAt Mr sp md cs ∗
      ⌜md.Index' = W64 0 ∨ cs = true⌝ ∗ ⌜uint.nat md.Index' < 2 ^ 64 - 1⌝ ∗
      ⌜(Mr.encSnap md).length < 2 ^ 40⌝ ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir { d with H := d.H ++ [WalOpG.snap md] }, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"SaveSnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗ WalFs.walOpenWFR P Mr w dir k ∗ ∃ d : WalDur, Q d ∗
          WalFs.walLenLb w dir (d.H.length + 1) ∗ WalFs.walSyncedLb dir (d.H.length + 1) }}

end spec

end EtcdGrove
end Perennial
