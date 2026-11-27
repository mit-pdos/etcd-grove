/-
`(*wal.WAL).encodeState` over `fsExt` (the torn-`Save` fix, fork `2bd3048d7`: `saveState`'s write, split
off so that `Save` writes a state record also when it is empty): the internal spec. Proved in
`Proof/.../wal/WAL__encodeState.lean`. Lean-first.
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

/-- **`w.encodeState(s)`** (S/wal.go:1305-1318): `w.state := s` and the next record of the tail not
yet encoded, `s`'s state record (also when `s` is empty), encoded; when it is the last (`rest = 1`), the
history's last index within the handle's indices. *Error*: the handle lost. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (hp : Loc)
    (hs : HardStateM),
  0 < h.rest →
  ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
      (fun x => (x.typ, x.data)) = some (stateType, Mr.encState hs) →
  (h.rest = 1 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi)) →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW ∗ walStIn P Mr hp hs ∗ ⌜hp ≠ null⌝ }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"encodeState")) (Val #hp))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (out' pend' : List w8) (sz' : Nat),
          walHandleIn P Mr w dir
            { h with rest := h.rest - 1, out := out', pend := pend', st := hs, sz := sz' } TailMetaW) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
