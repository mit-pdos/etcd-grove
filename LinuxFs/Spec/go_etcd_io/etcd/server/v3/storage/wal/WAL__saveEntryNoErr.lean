/-
`(*wal.WAL).saveEntry` with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`): `saveEntry.spec`'s
success arm over a semantics with no I/O error on the covered files (`FsStepSat (NoIoErr Sio)`, coverage
(a): every file of the roots' trees, `∀ st i, Sio.ino st i`), when the tail has room for the record's
frame (at most the data plus 64 bytes, `frame_walRecEnc_tight`). Proved in
`LinuxFs/Proof/.../wal/WAL__saveEntryNoErr.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
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

/-- **`w.saveEntry(e)` with no I/O error** (see the file header): `saveEntry.spec`'s success arm, `nil`
returned, when the tail's stream (written and pending) plus the record's data and 64 bytes ends at most at
`maxBytes`; the stream grows by at most that much. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.specNoErr (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (l : Loc) (e : EntryM),
  0 < h.rest → uint.nat e.Index' < 2 ^ 64 - 1 → (Mr.encEntry e).length < 2 ^ 40 →
  (h.rest = 1 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat e.Index') (uint.nat h.snapi)) →
  (((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
    (fun x => (x.typ, x.data)) = some (entryType, Mr.encEntry e)) →
  h.o0 + h.out.length + h.pend.length + ((Mr.encEntry e).length + 64) ≤ maxBytes →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW ∗ P.entIn l e }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"saveEntry")) (Val #l))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗ ∃ (out' pend' : List w8) (sz' : Nat),
          walHandleIn P Mr w dir
            { h with rest := h.rest - 1, out := out', pend := pend', enti := e.Index', sz := sz' }
            TailMetaW ∗
          ⌜out'.length + pend'.length ≤ h.out.length + h.pend.length + ((Mr.encEntry e).length + 64)⌝ }}

end spec

end EtcdGrove
end Perennial
