/-
`(*wal.WAL).saveEntry` over `fsExt` (W6 of `notes/wal-fsext-plan.md`): the internal spec. To be proved
in `LinuxFs/Proof/.../wal/WAL__saveEntry.lean`. Lean-first.
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

/-- **`w.saveEntry(e)`** (S/wal.go:1001-1010): the next record of the tail not yet encoded is `e`'s
entry record; encodes it (`MustMarshalMessage`, `encode`) and sets `w.enti` to its index. *Error*
(a write of the page writer): the handle lost. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (l : Loc) (e : EntryM),
  0 < h.rest →
  (((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
    (fun x => (x.typ, x.data)) = some (entryType, Mr.encEntry e)) →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h ∗ P.entIn l e }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"saveEntry")) (Val #l))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ out' pend' : List w8,
          walHandleIn P Mr w dir { h with rest := h.rest - 1, out := out', pend := pend', enti := e.Index' }) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
