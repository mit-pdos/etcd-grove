/-
`(*wal.WAL).sync` over `fsExt` (W6 of `notes/wal-fsext-plan.md`): the internal spec, over the handle's
state (`walHandleIn`). To be proved in `LinuxFs/Proof/.../wal/WAL__sync.lean`. Lean-first.
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

/-- **`w.sync()`** (S/wal.go:967-992) of a handle with every record of its history encoded
(`rest = 0`): the encoder's pending bytes flushed to the tail (`out ++ pend`, nothing pending; the
tail's size grown to cover them if they pass it), the tail fdatasynced: the history synced (`walSyncedLb
|H|`), the tail's resize window closed (the handle exact: `OsMeta.synced`). The window may be open before
(`TailMetaW`: a write past the preallocated size, W6 log, thirteenth session). *Error*: the handle lost. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS),
  h.rest = 0 →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walHandleIn P Mr w dir
          { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) } ∗
          WalFs.walSyncedLb dir h.H.length) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

/-- **`sync.spec` while the pending bytes fit the tail's size** (`o0 + |out ++ pend| ≤ sz`): what
the tail's writer accepts (`tailOk`) until writes past the preallocated size are covered (W6, after
`wal-zte2`'s relaxation); then `sync.spec` itself. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIn (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS),
  h.rest = 0 → h.o0 + h.out.length + h.pend.length ≤ h.sz →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walHandleIn P Mr w dir { h with out := h.out ++ h.pend, pend := [] } ∗
          WalFs.walSyncedLb dir h.H.length) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
