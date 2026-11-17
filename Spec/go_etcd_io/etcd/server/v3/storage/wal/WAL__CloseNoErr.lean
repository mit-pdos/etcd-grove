/-
`(*wal.WAL).Close()` with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`): `Close.spec` over a
semantics whose steps satisfy **no I/O error on chosen files** (`FsStepSat (NoIoErr Sio)`,
`GooseLang/Ext/Fs/Premises.lean`), with the coverage the user chose for now (2026-11-15, coverage (a),
`notes/decisions.md`, "fsExt: no I/O errors on chosen files"): every file of the roots' trees (etcd's data
directory), `∀ st i, Sio.ino st i`. etcd's server panics when `Close` fails (`onStop`'s `lg.Panic`,
`notes/wal-units/specgap.md` P1). Proved in `Proof/.../wal/WAL__CloseNoErr.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleRoom
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

/-- **`w.Close()` with no I/O error** (see the file header): `Close.spec`'s success arm, `nil` returned,
of a handle whose tail's pending bytes end at most at `maxBytes` (`walOpenWFR … 0`: a write reaching
ext4's `s_maxbytes` fails with `EFBIG`, which the premise does not exclude). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specNoErr (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ WalFs.walOpenWFR P Mr w dir 0 ∗ WalFs.walPurgeW w dir ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir d, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗ ∃ d : WalDur, Q d ∗ WalFs.walSyncedLb dir d.H.length ∗
        WalFs.walUnlockedTok ∗ osCallPerm (1 : Qp).half }}

end spec

end EtcdGrove
end Perennial
