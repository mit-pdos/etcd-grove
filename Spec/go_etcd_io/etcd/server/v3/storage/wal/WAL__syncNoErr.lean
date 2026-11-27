/-
`(*wal.WAL).sync` with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`): `sync.spec` and
`sync.specC` over a semantics whose steps satisfy **no I/O error on chosen files** (`FsStepSat (NoIoErr
Sio)`, `GooseLang/Ext/Fs/Premises.lean`), with the coverage the user chose for now (2026-11-15, coverage
(a), `notes/decisions.md`, "fsExt: no I/O errors on chosen files"): every file of the roots' trees (etcd's
data directory), `∀ st i, Sio.ino st i`. The flushed stream's end at most `maxBytes` (ext4's `s_maxbytes`:
a write reaching it fails with `EFBIG` whether or not the premise holds, since no write can succeed
there). Proved in `Proof/.../wal/WAL__syncNoErr.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncC
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

/-- **`w.sync()` with no I/O error** (see the file header): `sync.spec`'s success arm, always, when the
pending bytes end at most at `maxBytes`. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specNoErr (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS),
  h.rest = 0 → h.o0 + h.out.length + h.pend.length ≤ maxBytes →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗ walHandleIn P Mr w dir
          { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) } ∗
          WalFs.walSyncedLb dir h.inc h.H.length }}

/-- **`w.sync()` after `Close` closed the pipeline, with no I/O error** (`sync.specC`'s success arm,
always; see the file header). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specCNoErr (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (j : Ino) (h : WalHS)
    (nmd : Loc → Roots → Qp → IProp GF) (nf : Option GoString),
  h.rest = 0 → h.o0 + h.out.length + h.pend.length ≤ maxBytes →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleC P Mr w dir j h TailMetaW nmd nf }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗ walHandleC P Mr w dir j
          { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) }
          TailMetaS nmd nf ∗
          WalFs.walSyncedLb dir h.inc h.H.length }}

end spec

end EtcdGrove
end Perennial
