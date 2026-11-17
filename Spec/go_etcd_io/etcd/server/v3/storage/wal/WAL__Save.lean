/-
`(*wal.WAL).Save` over `fsExt` (W6 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean` restated with plan §3's binder changes:
over `fsExt`, the WAL layer (`walAreaOk`, `WalFs`'s vocabulary); the update at `walAuMask` (plan §11); the
error arm honest (Q6)). One spec since wal-link L1a (2026-11-17, `notes/wal-link-scope.md` §8: the former
`Save.spec` and `Save.specNoErr` merged), over a share of the handle (`walOpenWS`, `HandleShared.lean`: the
server's raft loop and apply thread use the WAL at once, serialized by `w.mu`), parameterised by the files
with no I/O error (`Sio`, `FsStepSat (NoIoErr Sio)`): the error arm only when `Sio` does not cover every
inode (`walCov`), and then only for the whole share; the room premise (`saveRoom`) only when it does. S/ =
`server/storage/wal/` at the pin with the local fork patches. Proved in
`Proof/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
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

open Classical in
/-- **The room used after a `Save` of `hs` and `es`** (`walUsed`, `HandleShared.lean`): kept by the shortcut
(an empty state and no entries: nothing written), none after a write (the tail ends below `2 ^ 43`: below
`SegmentSizeBytes`, or a cut's fresh segment). -/
def walUsedAfterSave (u : Nat) (hs : HardStateM) (es : List EntryM) : Nat :=
  if hsEmptyP hs ∧ es = [] then u else 0

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`raft.MustSync` over the client's hard states** (raft's `rawnode.go`: `entsnum != 0 ||
st.GetVote() != prevst.GetVote() || st.GetTerm() != prevst.GetTerm()`; a law of `P`, as
`WalPbIn.IsEmptyLaw`: the part cannot import the main tree's raft specs, plan §10). -/
abbrev WalPbIn.MustSyncLaw (P : WalPbIn GF) : Prop :=
  ∀ (p1 p2 : Loc) (h1 h2 : HardStateM) (n : w64),
  {{ P.hsIn p1 h1 ∗ P.hsIn p2 h2 }}
    (App (App (App (Val (@! go_etcd_io.raft.v3.MustSync)) (Val #p1)) (Val #p2)) (Val #n))
  {{ (b : Bool), RET #b; ⌜b = true ↔ (n ≠ W64 0 ∨ h1.Vote' ≠ h2.Vote' ∨ h1.Term' ≠ h2.Term')⌝ }}

/-- **A nil hard state, a fresh zero one** (`Save`'s `st == nil`/`w.state == nil` cases, S/wal.go:1100-1105):
a nil pointer holds only the zero state (`WalPbIn`'s "nil read as the zero state"), and a freshly
allocated `raftpb.HardState{}` holds it (a law of `P`: its hidden fields are the client's to keep). -/
abbrev WalPbIn.ZeroLaw (P : WalPbIn GF) : Prop :=
  (∀ hs : HardStateM, P.hsIn null hs ⊢ ⌜hs = hsZero⌝) ∧
  ∀ (p : Loc) (E : CoPset),
    p ↦ (zero_val go_etcd_io.raft.v3.raftpb.HardState) ⊢ |={E}=> P.hsIn p hsZero

/-- **`w.Save(st, ents)`** (S/wal.go:1075-1117): every entry index below `2^64-1` (a cut's name
would wrap, as the main tree's spec says), and each entry's encoding below `2^40` bytes (each record
must fit a frame, whose length field has 56 bits, and the encoder's `2^47`; ledger 2026-11-14, "no
bound on the records' size"). When `Sio` covers every inode, the batch's frames fit the handle's room
(`saveRoom … ≤ walSaveRoom`, the fresh room less the snapshots' budget: a write past ext4's `s_maxbytes`,
`fsExt`'s `maxBytes`, fails with `EFBIG` whatever the premise). The update carries the client's view of the
room the snapshot records used (`walUsed γ u`), which a writing `Save` frees (`walUsedAfterSave`). The update commits right after `w.mu.Lock()`, before any record is encoded (a
crash mid-call leaves an image of `H ++ [op]` past the mark, `walImg`); then the entries' records, `st`'s
unless empty (`saveState`), then a `sync` if `MustSync`, or a `cut` if the tail reached
`SegmentSizeBytes` (which syncs). `Save` of an empty state and no entries writes nothing (S/wal.go:1079)
while the model appends `save hsZero []` (no reader sees it). *Success*: the share, `Q d`, the history
written to its new length (`walLenLb`), and synced if the save must sync (`walMustSync`). *Error* (only
when `Sio` misses an inode, and then the caller holds the whole share: an I/O failure of a write, the
flush, the fdatasync, a `Seek` or the cut): the update has committed (`Q d`); the handle is lost (its
encoder may have written part of a frame; a write after a failed one would break the per-byte crash
invariant, plan §3), and with it the purge right and the lock token. `walMustSync`/`walSyncedLb` assume
`unsafeNoSync` false (the handle says so). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp) (hp : Loc)
    (hs : HardStateM) (sl : GoSlice) (esL : List Loc) (es : List EntryM) (sized : Bool)
    (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ ⌜walCov Sio ∨ q = 1⌝ ∗
      P.hsIn hp hs ∗ sl ↦*□ esL ∗ walEntsIn P esL es ∗ ⌜∀ e ∈ es, uint.nat e.Index' < 2 ^ 64 - 1⌝ ∗
      ⌜∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40⌝ ∗ ⌜walCov Sio → saveRoom Mr hs es ≤ walSaveRoom⌝ ∗
      AU <{ ∃∃ (d : WalDur) (u : Nat), WalFs.walDiskAt dir d ∗ ⌜d.sized = sized⌝ ∗ walUsed γ u }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir { d with H := d.H ++ [(WalOpG.save hs es).toRaw] } ∗
            walUsed γ (walUsedAfterSave u hs es), COMM Q d }> }}
    (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Save")) (Val #hp)) (Val #sl))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ ∃ d : WalDur, Q d ∗
          WalFs.walLenLb w dir (d.H.length + 1) ∗
          (⌜walMustSync (d.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir (d.H.length + 1))) ∨
      (⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ ∗ ∃ d : WalDur, Q d) }}

end spec

end EtcdGrove
end Perennial
