/-
`(*wal.WAL).Save` over `fsExt` (W6 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean` restated with plan §3's binder changes:
over `fsExt`, the WAL layer (`walAreaOk`, `WalFs`'s vocabulary) and the handle `walOpenWF`; the update
at `walAuMask` (plan §11); the error arm honest (Q6)). S/ = `server/storage/wal/` at the pin with the
local fork patches. To be proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`.
Lean-first.
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
bound on the records' size"; the batch bound of "the batch's size" is withdrawn: the tail's stream stays
below ext4's `s_maxbytes` by the writes' success, `fsExt`'s `maxBytes`). The update commits right after `w.mu.Lock()`, before any
record is encoded (a crash mid-call leaves an image of `H ++ [op]` past the mark, `walImg`); then
the entries' records, `st`'s unless empty (`saveState`), then a `sync` if `MustSync`, or a `cut`
if the tail reached `SegmentSizeBytes` (which syncs). `Save` of an empty state and no entries
writes nothing (S/wal.go:1079) while the model appends `save hsZero []` (no reader sees it).
*Success*: the handle, `Q d`, the history written to its new length (`walLenLb`), and synced if
the save must sync (`walMustSync`). *Error* (an I/O failure of a write, the flush, the fdatasync, a
`Seek` or the cut): the update has committed (`Q d`); the handle is lost (its encoder may have
written part of a frame; a write after a failed one would break the per-byte crash invariant,
plan §3), and with it the purge right and the lock token. `walMustSync`/`walSyncedLb` assume
`unsafeNoSync` false (the handle says so). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (hp : Loc) (hs : HardStateM)
    (sl : GoSlice) (esL : List Loc) (es : List EntryM) (sized : Bool) (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWF P Mr w dir ∗ P.hsIn hp hs ∗ sl ↦*□ esL ∗
      walEntsIn P esL es ∗ ⌜∀ e ∈ es, uint.nat e.Index' < 2 ^ 64 - 1⌝ ∗
      ⌜∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40⌝ ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir { d with H := d.H ++ [(WalOpG.save hs es).toRaw] }, COMM Q d }> }}
    (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Save")) (Val #hp)) (Val #sl))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walOpenWF P Mr w dir ∗ ∃ d : WalDur, Q d ∗
          WalFs.walLenLb w dir (d.H.length + 1) ∗
          (⌜walMustSync (d.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir (d.H.length + 1))) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ d : WalDur, Q d) }}

end spec

end EtcdGrove
end Perennial
