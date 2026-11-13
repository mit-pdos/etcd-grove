/-
`(*wal.WAL).saveState` over `fsExt` (W6 of `notes/wal-fsext-plan.md`): the internal spec. To be proved
in `LinuxFs/Proof/.../wal/WAL__saveState.lean`. Lean-first.
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

/-- **`w.saveState(s)`** (S/wal.go:1012-1020): of an empty hard state, nothing; else `w.state :=
s` and the next record of the tail not yet encoded, `s`'s state record, encoded. *Error*: the
handle lost. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (hp : Loc)
    (hs : HardStateM),
  (¬ hsEmptyP hs → 0 < h.rest ∧
    ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
      (fun x => (x.typ, x.data)) = some (stateType, Mr.encState hs)) →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h ∗ P.hsIn hp hs ∗ ⌜hp ≠ null⌝ }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"saveState")) (Val #hp))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil ∧ hsEmptyP hs⌝ ∗ walHandleIn P Mr w dir h) ∨
      (⌜err = GoInterface.nil ∧ ¬ hsEmptyP hs⌝ ∗ ∃ out' pend' : List w8,
          walHandleIn P Mr w dir { h with rest := h.rest - 1, out := out', pend := pend', st := hs }) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
