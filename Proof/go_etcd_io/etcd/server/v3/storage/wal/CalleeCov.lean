/- Lean-first (no Rocq counterpart).

# The callees' two specs, chosen by coverage (wal-link L1a, 2026-11-17; `notes/wal-link-scope.md` §8)

`Save`'s, `SaveSnapshot`'s and `Close`'s one spec each (over the shared handle, parameterised by `Sio`) call callees
whose families the link leaves for the queued cleanup: `saveEntry`, `saveState`, `sync` (and its `specC`), the encode on the tail (`encode.specTail`) each have a
`spec` (any I/O error) and a `specNoErr` (when `Sio` covers every inode, with a room premise). The lemmas
below are not specs: each derives, from a callee's two specs, the triple its caller uses at a call, the
room premise and bound only when `walCov Sio`, the error only when not (`WAL__Sync.lean` chooses inline).
They go when the cleanup collapses those families.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntryNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveStateNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__encodeStateNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__encodeState
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTailNoErr
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

/-- `encodeState` at a call (see the file header). -/
theorem walCov_encodeState (P : WalPbIn GF) (Mr : WalMarshal)
    (wp : go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.spec (W := W) P Mr)
    (wpNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.specNoErr (Sio := Sio) (W := W) P Mr)
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (hp : Loc)
    (hs : HardStateM) (h1 : 0 < h.rest)
    (h2 : ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
        (fun x => (x.typ, x.data)) = some (stateType, Mr.encState hs))
    (h3 : h.rest = 1 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi))
    (hroom : walCov Sio → h.o0 + h.out.length + h.pend.length + ((Mr.encState hs).length + 64) ≤ maxBytes) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW ∗ P.hsIn hp hs ∗ ⌜hp ≠ null⌝ }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"encodeState")) (Val #hp))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (out' pend' : List w8) (sz' : Nat),
          walHandleIn P Mr w dir
            { h with rest := h.rest - 1, out := out', pend := pend', st := hs, sz := sz' } TailMetaW ∗
          ⌜walCov Sio →
            out'.length + pend'.length ≤ h.out.length + h.pend.length + ((Mr.encState hs).length + 64)⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }} := by
  iintro %Φ Hpre HΦ
  by_cases hc : walCov Sio
  · iapply (wpNE hc R jr r w dir h hp hs h1 h2 h3 (hroom hc)) $$ Hpre
    inext
    iintro %err ⟨%herr, %out', %pend', %sz', Hh, %hl⟩
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact herr
    iexists out', pend', sz'
    iframe Hh
    ipureintro; exact fun _ => hl
  · iapply (wp R jr r w dir h hp hs h1 h2 h3) $$ Hpre
    inext
    iintro %err (⟨%herr, %out', %pend', %sz', Hh⟩ | %herr)
    · iapply HΦ; ileft
      isplitr
      · ipureintro; exact herr
      iexists out', pend', sz'
      iframe Hh
      ipureintro; exact fun h => absurd h hc
    · iapply HΦ; iright
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

/-- `sync` after `Close` closed the pipeline, at a call (see the file header). -/
theorem walCov_syncC (P : WalPbIn GF) (Mr : WalMarshal)
    (wp : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specC (W := W) P Mr)
    (wpNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specCNoErr (Sio := Sio) (W := W) P Mr)
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (j : Ino) (h : WalHS)
    (nmd : Loc → Roots → Qp → IProp GF) (nf : Option GoString) (h1 : h.rest = 0)
    (hroom : walCov Sio → h.o0 + h.out.length + h.pend.length ≤ maxBytes) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleC P Mr w dir j h TailMetaW nmd nf }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walHandleC P Mr w dir j
          { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) }
          TailMetaS nmd nf ∗
          WalFs.walSyncedLb dir h.H.length) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }} := by
  iintro %Φ Hpre HΦ
  by_cases hc : walCov Sio
  · iapply (wpNE hc R jr r w dir j h nmd nf h1 (hroom hc)) $$ Hpre
    inext
    iintro %err ⟨%herr, Hh, #Hs⟩
    iapply HΦ
    ileft
    iframe Hh Hs
    ipureintro; exact herr
  · iapply (wp R jr r w dir j h nmd nf h1) $$ Hpre
    inext
    iintro %err (⟨%herr, Hh, #Hs⟩ | ⟨%herr, -⟩)
    · iapply HΦ
      ileft
      iframe Hh Hs
      ipureintro; exact herr
    · iapply HΦ
      iright
      ipureintro; exact ⟨herr, hc⟩

/-- The record's encode on the tail at a call (see the file header). -/
theorem walCov_encodeTail (Mr : WalMarshal)
    (wp : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTail (W := W) Mr)
    (wpNE : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTailNoErr (Sio := Sio) (W := W) Mr)
    (R : Roots) (jr : Ino) (r : GoString) (e f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat)
    (out pend : List w8) (c : w32) (rp : Loc) (t : w64) (d : List w8)
    (h1 : recSize (recOf ⟨t, hash.crc32.crc32c c d, d⟩) < 2 ^ 47)
    (h2 : out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩) <+: (tailStream Mr H md cuts).drop o0)
    (h3 : o0 + out.length ≤ sz) (h4 : sz ≤ 0xffffffff000)
    (hroom : walCov Sio → o0 + (out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)).length ≤ maxBytes) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ encEnv ∗ ownEncoder e (wal.fileWi f) c pend ∗
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out TailMetaW ∗ encRecIn rp t d }}
    (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.encoder.ty @!!
      go!"encode")) (Val #rp))
  {{ (err : GoInterface), RET #err;
      ∃ pend' : List w8, ownEncoder e (wal.fileWi f) (hash.crc32.crc32c c d) pend' ∗
        recRoC rp (recOf ⟨t, hash.crc32.crc32c c d, d⟩) ∗
        ((∃ (out' : List w8) (sz' : Nat), ⌜err = GoInterface.nil ∧
            out' ++ pend' = out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩) ∧
            o0 + out'.length ≤ sz' ∧ sz' ≤ 0xffffffff000⌝ ∗
            walTailW (W := W) f fd name dir γ i H md cuts o0 sz' out' TailMetaW) ∨
         ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝) }} := by
  iintro %Φ Hpre HΦ
  by_cases hc : walCov Sio
  · iapply (wpNE hc R jr r e f fd name dir γ i H md cuts o0 sz out pend c rp t d h1 h2 h3 h4 (hroom hc)) $$ Hpre
    inext
    iintro %err ⟨%pend', He, Hrec, %out', %sz', %hp, Htw⟩
    iapply HΦ
    iexists pend'
    iframe He Hrec
    ileft
    iexists out', sz'
    iframe Htw
    ipureintro; exact hp
  · iapply (wp R jr r e f fd name dir γ i H md cuts o0 sz out pend c rp t d h1 h2 h3 h4) $$ Hpre
    inext
    iintro %err ⟨%pend', He, Hrec, Hres⟩
    iapply HΦ
    iexists pend'
    iframe He Hrec
    icases Hres with (Hok | %herr)
    · ileft; iexact Hok
    · iright; ipureintro; exact ⟨herr, hc⟩

/-! ### The tail's offset test, shared by `Save` and `SaveSnapshot` (both cut once the tail passes
`SegmentSizeBytes`) -/

/-- A small stream leaves the fresh room. -/
theorem save_room_small (a b c : Nat) (h : a + b + c ≤ 2 ^ 43) : a + b + c + walFreshRoom ≤ maxBytes := by
  unfold walFreshRoom
  have : (2 : Nat) ^ 43 ≤ maxBytes := by decide
  omega

/-- An offset below ext4's maximum, as a signed word (`cut`'s `cut_off_toInt`). -/
theorem save_off_toInt (a b : Nat) (h : a + b ≤ 0xffffffff000) :
    0 ≤ (W64 ((a : Int) + (b : Int))).toInt ∧ (W64 ((a : Int) + (b : Int))).toInt ≤ 0xffffffff000 ∧
      (W64 ((a : Int) + (b : Int))).toInt = a + b := by
  have : (W64 ((a : Int) + (b : Int))).toInt = a + b := by
    word
  omega

/-- `Save`'s offset test, below the segment size. -/
theorem save_hif (a b : Nat) (hx : (W64 ((a : Int) + (b : Int))).toInt = a + b)
    (h : sint.Z (W64 ((a : Int) + (b : Int))) < sint.Z (W64 64000000)) : a + b < 64000000 := by
  have e1 : sint.Z (W64 ((a : Int) + (b : Int))) = ((a + b : Nat) : Int) := by
    rw [show sint.Z (W64 ((a : Int) + (b : Int))) = (W64 ((a : Int) + (b : Int))).toInt from rfl, hx]; simp
  have e2 : sint.Z (W64 64000000) = 64000000 := by decide
  rw [e1, e2] at h; omega

/-- `walPc_bound`, keeping the receipt. -/
theorem save_pc_bound (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (n : Nat) :
    ⊢@{IProp GF} WalFs.walAreaOk walCodec Mr R jr r -∗ ⧗ (n + 1) -∗ ⧗ (n + 1) ∗ ⌜n + 2 < 2 ^ 63⌝ := by
  iintro #Harea Hr
  have H := persistent_entails_left (PROP := IProp GF)
    (P := iprop(WalFs.walAreaOk walCodec Mr R jr r ∗ ⧗ (n + 1))) (Q := iprop(⌜n + 2 < 2 ^ 63⌝))
    (by iintro ⟨#Ha, Hr⟩; iapply (walPc_bound walCodec Mr R jr r n) $$ Ha Hr)
  ihave Hx := H $$ [Hr]
  · iframe Harea Hr
  icases Hx with ⟨⟨-, Hr⟩, %hb⟩
  iframe Hr; ipureintro; exact hb

end calls

end EtcdGrove
end Perennial
