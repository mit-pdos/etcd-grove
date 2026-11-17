/-
`(*wal.WAL).Save` with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`): `Save.spec`'s success
arm over a semantics with no I/O error on the covered files (`FsStepSat (NoIoErr Sio)`, coverage (a): every
file of the roots' trees, `∀ st i, Sio.ino st i`), from a handle with room for the batch's frames
(`walOpenWFR`, `saveRoom`); the handle comes back with the fresh room (`walFreshRoom`, about 8 TB) unless
the call wrote nothing. etcd's server panics when `Save` fails (its raft loop's `storage.Save`). Proved in
`Proof/.../wal/WAL__SaveNoErr.lean`, over `cut.specNoErr` (not proved: the lock call). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleRoom
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section pure
variable [GooseExts]

/-- **The room a `Save` of `hs` and `es` needs**: each record's frame is at most its data plus 64 bytes
(`frame_walRecEnc_tight`): the entries' and the state's. -/
def saveRoom (Mr : WalMarshal) (hs : HardStateM) (es : List EntryM) : Nat :=
  (es.map (fun e => (Mr.encEntry e).length + 64)).sum + ((Mr.encState hs).length + 64)

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`w.Save(st, ents)` with no I/O error** (see the file header): `Save.spec`'s success arm, `nil`
returned, from a handle with room `k` for the batch (`saveRoom Mr hs es ≤ k`). The handle comes back with
room `k` when `Save` wrote nothing (an empty state and no entries, S/wal.go:1079), else with the fresh room
`walFreshRoom`: either the tail stayed below `SegmentSizeBytes` (64 MB, its pending bytes at most the page
writer's buffer) or the call cut a new segment, whose headers end below `2 ^ 43`. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.specNoErr (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (hp : Loc) (hs : HardStateM)
    (sl : GoSlice) (esL : List Loc) (es : List EntryM) (sized : Bool) (Q : WalDur → IProp GF) (k : Nat),
  saveRoom Mr hs es ≤ k →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ WalFs.walOpenWFR P Mr w dir k ∗ P.hsIn hp hs ∗ sl ↦*□ esL ∗
      walEntsIn P esL es ∗ ⌜∀ e ∈ es, uint.nat e.Index' < 2 ^ 64 - 1⌝ ∗
      ⌜∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40⌝ ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir { d with H := d.H ++ [(WalOpG.save hs es).toRaw] }, COMM Q d }> }}
    (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Save")) (Val #hp)) (Val #sl))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗
      ((⌜hsEmptyP hs ∧ es = []⌝ ∗ WalFs.walOpenWFR P Mr w dir k) ∨
        (⌜¬ (hsEmptyP hs ∧ es = [])⌝ ∗ WalFs.walOpenWFR P Mr w dir walFreshRoom)) ∗
      ∃ d : WalDur, Q d ∗ WalFs.walLenLb w dir (d.H.length + 1) ∗
          (⌜walMustSync (d.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir (d.H.length + 1)) }}

end spec

end EtcdGrove
end Perennial
