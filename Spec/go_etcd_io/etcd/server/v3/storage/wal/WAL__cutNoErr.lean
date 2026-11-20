/-
`(*wal.WAL).cut` with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`): `cut.spec`'s success arm
over a semantics with no I/O error on the covered files (`FsStepSat (NoIoErr Sio)`, coverage (a),
`∀ st i, Sio.ino st i`), when the old tail's stream ends at most at `maxBytes` (its `sync`).

**Not proved** (no proof file): `cut` locks the new segment (`fileutil.LockFile`, step 8 of S/wal.go:875-965, an OFD lock
or `flock` request), and `NoIoErr` does not cover the lock calls (`IoCovers` names neither `OfdLock` nor
`Flock`; the lock semantics lets a request fail with any errno at any time). Whether to extend the premise
to them is the user's decision (`notes/wal-units/noioerr.md`, third session). `Save.spec` (its covered case) is proved
over this spec. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cut
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

/-- **`w.cut()` with no I/O error** (see the file header): `cut.spec`'s success arm, `nil` returned,
when the old tail's stream (written and pending) ends at most at `maxBytes`. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.specNoErr (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS),
  h.rest = 0 → h.st = walLastHS (h.H.map WalOpG.toM) → h.pc + 2 < 2 ^ 63 →
  (∀ b ∈ h.cuts, b < h.H.length) → h.cuts.Pairwise (· < ·) →
  walCutPos (h.H.map WalOpG.toM) h.H.length → 0 < h.H.length →
  h.md.length + (Mr.encState h.st).length < 2 ^ 42 →
  h.o0 + h.out.length + h.pend.length ≤ maxBytes →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"cut")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗ ∃ h' : WalHS, walHandleIn P Mr w dir h' ∗
          ⌜h'.H = h.H ∧ h'.md = h.md ∧ h'.cuts = h.cuts ++ [h.H.length] ∧ h'.rest = 0 ∧ h'.st = h.st ∧
            h'.enti = h.enti ∧ h'.snapi = h.snapi ∧ h'.pc = h.pc + 1 ∧
            h'.o0 + h'.out.length + h'.pend.length ≤ 2 ^ 43⌝ ∗ WalFs.walSyncedLb dir h.H.length }}

end spec

end EtcdGrove
end Perennial
