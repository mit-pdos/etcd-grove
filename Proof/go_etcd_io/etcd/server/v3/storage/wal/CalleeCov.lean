/- Lean-first (no Rocq counterpart).

# The callees' two specs, chosen by coverage (wal-link L1a, 2026-11-17; `notes/wal-link-scope.md` §8)

`Save`'s and `SaveSnapshot`'s one spec each (over the shared handle, parameterised by `Sio`) call callees
whose families the link leaves for the queued cleanup: `saveEntry`, `saveState`, `sync`, `cut` each have a
`spec` (any I/O error) and a `specNoErr` (when `Sio` covers every inode, with a room premise). The lemmas
below are not specs: each derives, from a callee's two specs, the triple its caller uses at a call, the
room premise and bound only when `walCov Sio`, the error only when not (`WAL__Sync.lean` chooses inline).
They go when the cleanup collapses those families.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntryNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveStateNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutNoErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic
open Fs WalEnc WalFs

section calls
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- `saveEntry` at a call (see the file header). -/
theorem walCov_saveEntry (P : WalPbIn GF) (Mr : WalMarshal)
    (wp : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.spec (W := W) P Mr)
    (wpNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.specNoErr (Sio := Sio) (W := W) P Mr)
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (l : Loc) (e : EntryM)
    (h1 : 0 < h.rest) (h2 : uint.nat e.Index' < 2 ^ 64 - 1) (h3 : (Mr.encEntry e).length < 2 ^ 40)
    (h4 : h.rest = 1 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat e.Index') (uint.nat h.snapi))
    (h5 : ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
      (fun x => (x.typ, x.data)) = some (entryType, Mr.encEntry e))
    (hroom : walCov Sio → h.o0 + h.out.length + h.pend.length + ((Mr.encEntry e).length + 64) ≤ maxBytes) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW ∗ P.entIn l e }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"saveEntry")) (Val #l))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (out' pend' : List w8) (sz' : Nat),
          walHandleIn P Mr w dir
            { h with rest := h.rest - 1, out := out', pend := pend', enti := e.Index', sz := sz' }
            TailMetaW ∗
          ⌜walCov Sio →
            out'.length + pend'.length ≤ h.out.length + h.pend.length + ((Mr.encEntry e).length + 64)⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }} := by
  iintro %Φ Hpre HΦ
  by_cases hc : walCov Sio
  · iapply (wpNE hc R jr r w dir h l e h1 h2 h3 h4 h5 (hroom hc)) $$ Hpre
    inext
    iintro %err ⟨%herr, %out', %pend', %sz', Hh, %hl⟩
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact herr
    iexists out', pend', sz'
    iframe Hh
    ipureintro; exact fun _ => hl
  · iapply (wp R jr r w dir h l e h1 h2 h3 h4 h5) $$ Hpre
    inext
    iintro %err (⟨%herr, %out', %pend', %sz', Hh⟩ | %herr)
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact herr
      iexists out', pend', sz'
      iframe Hh
      ipureintro; exact fun h => absurd h hc
    · iapply HΦ
      iright
      ipureintro; exact ⟨herr, hc⟩

/-- `saveState` at a call (see the file header). -/
theorem walCov_saveState (P : WalPbIn GF) (Mr : WalMarshal)
    (wp : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (W := W) P Mr)
    (wpNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.specNoErr (Sio := Sio) (W := W) P Mr)
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (hp : Loc)
    (hs : HardStateM)
    (h1 : ¬ hsEmptyP hs → 0 < h.rest ∧
      ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
        (fun x => (x.typ, x.data)) = some (stateType, Mr.encState hs) ∧
      (h.rest = 1 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi)))
    (hroom : walCov Sio → h.o0 + h.out.length + h.pend.length + ((Mr.encState hs).length + 64) ≤ maxBytes) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW ∗ P.hsIn hp hs ∗ ⌜hp ≠ null⌝ }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"saveState")) (Val #hp))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil ∧ hsEmptyP hs⌝ ∗ walHandleIn P Mr w dir h TailMetaW) ∨
      (⌜err = GoInterface.nil ∧ ¬ hsEmptyP hs⌝ ∗ ∃ (out' pend' : List w8) (sz' : Nat),
          walHandleIn P Mr w dir
            { h with rest := h.rest - 1, out := out', pend := pend', st := hs, sz := sz' } TailMetaW ∗
          ⌜walCov Sio →
            out'.length + pend'.length ≤ h.out.length + h.pend.length + ((Mr.encState hs).length + 64)⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }} := by
  iintro %Φ Hpre HΦ
  by_cases hc : walCov Sio
  · iapply (wpNE hc R jr r w dir h hp hs h1 (hroom hc)) $$ Hpre
    inext
    iintro %err ⟨%herr, Hres⟩
    iapply HΦ
    icases Hres with (⟨%hse, Hh⟩ | ⟨%hse, %out', %pend', %sz', Hh, %hl⟩)
    · ileft; iframe Hh; ipureintro; exact ⟨herr, hse⟩
    · iright; ileft
      isplitr
      · ipureintro; exact ⟨herr, hse⟩
      iexists out', pend', sz'
      iframe Hh
      ipureintro; exact fun _ => hl
  · iapply (wp R jr r w dir h hp hs h1) $$ Hpre
    inext
    iintro %err (⟨%herr, Hh⟩ | ⟨%herr, %out', %pend', %sz', Hh⟩ | %herr)
    · iapply HΦ; ileft; iframe Hh; ipureintro; exact herr
    · iapply HΦ; iright; ileft
      isplitr
      · ipureintro; exact herr
      iexists out', pend', sz'
      iframe Hh
      ipureintro; exact fun h => absurd h hc
    · iapply HΦ; iright; iright
      ipureintro; exact ⟨herr, hc⟩

/-- `sync` at a call (see the file header). -/
theorem walCov_sync (P : WalPbIn GF) (Mr : WalMarshal)
    (wp : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wpNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specNoErr (Sio := Sio) (W := W) P Mr)
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (h1 : h.rest = 0)
    (hroom : walCov Sio → h.o0 + h.out.length + h.pend.length ≤ maxBytes) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walHandleIn P Mr w dir
          { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) } ∗
          WalFs.walSyncedLb dir h.H.length) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }} := by
  iintro %Φ Hpre HΦ
  by_cases hc : walCov Sio
  · iapply (wpNE hc R jr r w dir h h1 (hroom hc)) $$ Hpre
    inext
    iintro %err ⟨%herr, Hh, #Hs⟩
    iapply HΦ
    ileft
    iframe Hh Hs
    ipureintro; exact herr
  · iapply (wp R jr r w dir h h1) $$ Hpre
    inext
    iintro %err (⟨%herr, Hh, #Hs⟩ | %herr)
    · iapply HΦ
      ileft
      iframe Hh Hs
      ipureintro; exact herr
    · iapply HΦ
      iright
      ipureintro; exact ⟨herr, hc⟩

/-- `cut` at a call (see the file header). -/
theorem walCov_cut (P : WalPbIn GF) (Mr : WalMarshal)
    (wp : go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (W := W) P Mr)
    (wpNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.specNoErr (Sio := Sio) (W := W) P Mr)
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS)
    (h1 : h.rest = 0) (h2 : h.st = walLastHS (h.H.map WalOpG.toM)) (h3 : h.pc + 2 < 2 ^ 63)
    (h4 : ∀ b ∈ h.cuts, b < h.H.length) (h5 : h.cuts.Pairwise (· < ·))
    (h6 : walCutPos (h.H.map WalOpG.toM) h.H.length) (h7 : 0 < h.H.length)
    (h8 : h.md.length + (Mr.encState h.st).length < 2 ^ 42)
    (hroom : walCov Sio → h.o0 + h.out.length + h.pend.length ≤ maxBytes) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"cut")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ h' : WalHS, walHandleIn P Mr w dir h' ∗
          ⌜h'.H = h.H ∧ h'.md = h.md ∧ h'.cuts = h.cuts ++ [h.H.length] ∧ h'.rest = 0 ∧ h'.st = h.st ∧
            h'.enti = h.enti ∧ h'.snapi = h.snapi ∧ h'.pc = h.pc + 1 ∧
            h'.o0 + h'.out.length + h'.pend.length ≤ 2 ^ 43⌝ ∗ WalFs.walSyncedLb dir h.H.length) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }} := by
  iintro %Φ Hpre HΦ
  by_cases hc : walCov Sio
  · iapply (wpNE hc R jr r w dir h h1 h2 h3 h4 h5 h6 h7 h8 (hroom hc)) $$ Hpre
    inext
    iintro %err ⟨%herr, Hres⟩
    iapply HΦ
    ileft
    iframe Hres
    ipureintro; exact herr
  · iapply (wp R jr r w dir h h1 h2 h3 h4 h5 h6 h7 h8) $$ Hpre
    inext
    iintro %err (⟨%herr, Hres⟩ | %herr)
    · iapply HΦ
      ileft
      iframe Hres
      ipureintro; exact herr
    · iapply HΦ
      iright
      ipureintro; exact ⟨herr, hc⟩

end calls

end EtcdGrove
end Perennial
