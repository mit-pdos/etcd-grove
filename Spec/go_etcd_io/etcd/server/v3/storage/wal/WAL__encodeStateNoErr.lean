/-
`(*wal.WAL).encodeState` with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`): `encodeState.spec`'s
success arms over a semantics with no I/O error on the covered files (`FsStepSat (NoIoErr Sio)`, coverage
(a), `∀ st i, Sio.ino st i`), when the tail has room for the record's frame. Proved in
`Proof/.../wal/WAL__encodeStateNoErr.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__encodeState
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

/-- **`w.encodeState(s)`, no I/O error** (every inode in `Sio`): `encodeState.spec`'s success, the room
covering the record's frame. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.specNoErr (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (hp : Loc)
    (hs : HardStateM),
  0 < h.rest →
  ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
      (fun x => (x.typ, x.data)) = some (stateType, Mr.encState hs) →
  (h.rest = 1 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi)) →
  h.o0 + h.out.length + h.pend.length + ((Mr.encState hs).length + 64) ≤ maxBytes →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW ∗ walStIn P Mr hp hs ∗ ⌜hp ≠ null⌝ }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"encodeState")) (Val #hp))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗ ∃ (out' pend' : List w8) (sz' : Nat),
          walHandleIn P Mr w dir
            { h with rest := h.rest - 1, out := out', pend := pend', st := hs, sz := sz' } TailMetaW ∗
          ⌜out'.length + pend'.length ≤ h.out.length + h.pend.length + ((Mr.encState hs).length + 64)⌝ }}

end spec

end EtcdGrove
end Perennial
