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

/-- **`pbutil.MustMarshalMessage` of an entry** (S/wal.go:1002): a fresh non-nil slice of its encoding
(`Mr.encEntry`, the bytes the WAL's entry record holds). A law of `P`, as `WalPbIn.MarshalHsLaw` of a hard
state (`WAL__cutPre.lean`), which `saveState` uses: the part cannot import the main tree's specs of
`pbutil.MustMarshalMessage` over raft's messages (plan §10); to discharge at C6. A hypothesis of
`saveEntry`'s proof. -/
abbrev WalPbIn.MarshalEntLaw (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (l : Loc) (e : EntryM),
  {{ P.entIn l e }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Entry.ty) #l)))
  {{ (d : GoSlice), RET #d; d ↦* Mr.encEntry e ∗ ownSliceCap w8 d (DFrac.own 1) ∗ ⌜d ≠ slice.nil⌝ }}

/-- **`e.GetIndex()` of an entry** (S/wal.go:1008): its index. A law of `P` (as `MarshalEntLaw`); a
hypothesis of `saveEntry`'s proof. -/
abbrev WalPbIn.GetIndexLaw (P : WalPbIn GF) : Prop :=
  ∀ (l : Loc) (e : EntryM),
  {{ P.entIn l e }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Entry.ty @!! go!"GetIndex")) (Val #()))
  {{ RET #e.Index'; True }}

/-- **`w.saveEntry(e)`** (S/wal.go:1001-1010): the next record of the tail not yet encoded is `e`'s
entry record; encodes it (`MustMarshalMessage`, `encode`) and sets `w.enti` to its index (below
`2^64-1`, `Save`'s premise). When it is the last record (`rest = 1`), the history's last index is
at most the larger of its index and `w.snapi` (the handle's bound at `rest = 0`; `Save` has it: the
entry is the operation's last, and `walMaxSnapIdx ≤ snapi`). No bound on the tail's stream (withdrawn
2026-11-14: a write never lands past ext4's `s_maxbytes`, `fsExt`'s `maxBytes`). The tail's resize window may be open, before and after
(`TailMetaW`: a write past the preallocated size opens one, W6 log, thirteenth session), its size `sz'`
grown with the writes. *Error* (a write of the page writer): the handle lost. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS) (l : Loc) (e : EntryM),
  0 < h.rest → uint.nat e.Index' < 2 ^ 64 - 1 →
  (h.rest = 1 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat e.Index') (uint.nat h.snapi)) →
  (((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
    (fun x => (x.typ, x.data)) = some (entryType, Mr.encEntry e)) →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h TailMetaW ∗ P.entIn l e }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"saveEntry")) (Val #l))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (out' pend' : List w8) (sz' : Nat),
          walHandleIn P Mr w dir
            { h with rest := h.rest - 1, out := out', pend := pend', enti := e.Index', sz := sz' }
            TailMetaW) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
