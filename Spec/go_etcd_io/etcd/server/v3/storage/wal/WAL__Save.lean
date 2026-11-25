/-
`(*wal.WAL).Save` over `fsExt` (W6 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean` restated with plan §3's binder changes:
over `fsExt`, the WAL layer (`walAreaOk`, `WalFs`'s vocabulary); the update at `walAuMask` (plan §11); the
error arm honest (Q6)). One spec since wal-link L1a (2026-11-17, `notes/wal-link-scope.md` §8: the former
`Save.spec` and `Save.specNoErr` merged), over a share of the handle (`walOpenWS`, `HandleShared.lean`: the
server's raft loop and apply thread use the WAL at once, serialized by `w.mu`), parameterised by the files
with no I/O error (`Sio`, `FsStepSat (NoIoErr Sio)`): the error arm only when `Sio` does not cover every
inode (`walCov`), and then only for the whole share; a batch above `MaxSaveBatchBytes` refused before the
lock (fork fix 0009, 2026-11-19: the former room premise `walCov Sio → saveRoom … ≤ walFreshRoom` gone). S/ =
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

/-- **The bytes `Save`'s pre-lock check counts** (fix 0009, S/wal.go `Save`'s first loop): each entry's
`proto.Size` (its encoding, `SizeLaw`) plus `saveEntryOverhead` (64). -/
def saveBatchBytes (Mr : WalMarshal) (es : List EntryM) : Nat :=
  (es.map (fun e => (Mr.encEntry e).length + 64)).sum

/-- **`MaxSaveBatchBytes`** (fix 0009: `1 << 42`, a `var` only tests assign; `wal.walInit`). -/
def maxSaveBatch : Nat := 2 ^ 42

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)]

/-- **`raft.MustSync` over the client's hard states** (raft's `rawnode.go`: `entsnum != 0 ||
st.GetVote() != prevst.GetVote() || st.GetTerm() != prevst.GetTerm()`; a law of `P`, as
`WalPbIn.IsEmptyLaw`: the part cannot import the main tree's raft specs, plan §10). -/
abbrev WalPbIn.MustSyncLaw (P : WalPbIn GF) : Prop :=
  ∀ (p1 p2 : Loc) (h1 h2 : HardStateM) (n : w64),
  {{ P.hsIn p1 h1 ∗ P.hsIn p2 h2 }}
    (App (App (App (Val (@! go_etcd_io.raft.v3.MustSync)) (Val #p1)) (Val #p2)) (Val #n))
  {{ (b : Bool), RET #b; ⌜b = true ↔ (n ≠ W64 0 ∨ h1.Vote' ≠ h2.Vote' ∨ h1.Term' ≠ h2.Term')⌝ }}

/-- **`proto.Size(e)` of an entry** (`Save`'s pre-lock check, fix 0009): the length of its encoding as
`MustMarshalMessage` writes it (`MarshalEntLaw`), when below `2^63` (Go's `int` sum wraps above, as
`proto.SizePb.spec` says). A law of `P` (as `MarshalEntLaw`); discharged for raft's entries from
`proto.SizePb.spec` (`RaftModel/LawsEnt.lean`). -/
abbrev WalPbIn.SizeLaw (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (l : Loc) (e : EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ P.entIn l e }}
    (App (Val (@! google_golang_org.protobuf.proto.Size))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Entry.ty) #l)))
  {{ (n : w64), RET #n; ⌜(Mr.encEntry e).length < 2 ^ 63 → sint.Z n = (Mr.encEntry e).length⌝ }}

/-- **A nil hard state, a fresh zero one** (`Save`'s `st == nil`/`w.state == nil` cases, S/wal.go:1100-1105):
a nil pointer holds only the zero state (`WalPbIn`'s "nil read as the zero state"), and a freshly
allocated `raftpb.HardState{}` holds it (a law of `P`: its hidden fields are the client's to keep). -/
abbrev WalPbIn.ZeroLaw (P : WalPbIn GF) : Prop :=
  (∀ hs : HardStateM, P.hsIn null hs ⊢ ⌜hs = hsZero⌝) ∧
  ∀ (p : Loc) (E : CoPset),
    p ↦ (zero_val go_etcd_io.raft.v3.raftpb.HardState) ⊢ |={E}=> P.hsIn p hsZero

/-- **A fresh zero hard state marshals to the zero state's encoding** (P6, the torn-`Save` fix: `Save`'s
`w.state = &raftpb.HardState{}`, whose state record `encodeState` may write; `walStIn`). As `ZeroLaw.2`,
with `walStMarsh`. Discharged for raft's instance from `proto.MarshalPb.spec` (non-nil for a non-nil
message: `RaftModel/LawsHsMarshal.lean`). -/
abbrev WalPbIn.ZeroStLaw (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (p : Loc) (E : CoPset),
    p ↦ (zero_val go_etcd_io.raft.v3.raftpb.HardState) ⊢ |={E}=> P.hsIn p hsZero ∗ walStMarsh Mr p hsZero

/-- **`w.Save(st, ents)`** (S/wal.go:1115-1160): every entry index below `2^64-1` (a cut's name
would wrap, as the main tree's spec says), and each entry's encoding below `2^40` bytes (each record
must fit a frame, whose length field has 56 bits, and the encoder's `2^47`; ledger 2026-11-14, "no
bound on the records' size"). First (fix 0009) the batch's bytes (`saveBatchBytes`: each entry's
`proto.Size` plus 64) are summed; past `MaxSaveBatchBytes` (`maxSaveBatch`, 4 TiB) `Save` returns
`ErrSaveBatchTooLarge` before `w.mu.Lock()`: nothing committed or written, the share back (*Refused*);
the update is needed only for a batch that passes (`⌜saveBatchBytes … ≤ maxSaveBatch⌝ -∗ AU`), so a
caller holding one keeps it when the batch is too large (it splits on the size first, and passes the
update only for a batch that fits: there the refusal is impossible). A batch that passes fits the room a fresh tail leaves (`saveRoom … ≤ walFreshRoom`:
a write past ext4's `s_maxbytes`, `fsExt`'s `maxBytes`, fails with `EFBIG`). The update commits right after `w.mu.Lock()`, before any record is encoded (a
crash mid-call leaves an image of `H ++ [op]` past the mark, `walImg`); then the entries' records, `st`'s
unless empty (`saveState`), then a `sync` if `MustSync`, or a `cut` if the tail reached
`SegmentSizeBytes` (which syncs; `cut.spec`'s premises: the lock and map premise at `Sio`,
`FsStepSat (NoMapLockErr Sio)`, and, when `Sio` covers every inode, the WAL directory fitting, `DirFits dir`,
with its children's paths in `Sio`: `WalA.fits`/`covP`). `Save` of an empty state and no entries writes nothing (S/wal.go:1079)
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
  (walCov Sio → DirFits dir ∧ ∀ b, Sio.path (child dir b)) →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ ⌜walCov Sio ∨ q = 1⌝ ∗
      P.hsIn hp hs ∗ sl ↦*□ esL ∗ walEntsIn P esL es ∗ ⌜∀ e ∈ es, uint.nat e.Index' < 2 ^ 64 - 1⌝ ∗
      ⌜∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40⌝ ∗
      (⌜saveBatchBytes Mr es ≤ maxSaveBatch⌝ -∗
        AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
          <{ WalFs.walDiskAtI dir γ.inc { d with H := d.H ++ [(WalOpG.save hs es).toRaw] }, COMM Q d }>) }}
    (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Save")) (Val #hp)) (Val #sl))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ ∃ d : WalDur, Q d ∗
          WalFs.walLenLb w dir γ.inc (d.H.length + 1) ∗
          (⌜walMustSync (d.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir γ.inc (d.H.length + 1))) ∨
      (⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ ∗ ∃ d : WalDur, Q d) ∨
      (⌜err ≠ GoInterface.nil ∧ maxSaveBatch < saveBatchBytes Mr es⌝ ∗ walOpenWS Sio P Mr w dir γ q) }}

end spec

end EtcdGrove
end Perennial
