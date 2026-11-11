/-
**The WAL's resources over its history** (WAL W4a, 2026-11-11; the approved W4 Draft's §1.2, §1.4,
§1.5; `notes/decisions.md`, "WAL W4a"). Lean-first. The vocabulary of the WAL's trust-boundary specs
(`Spec/go_etcd_io/etcd/server/v3/storage/wal/`): the abstract-disk extension's points-to read over
`WalHist` (`walDisk`), the read path's snapshot lists, the `walpb.Snapshot` pointer predicate, and
the purge law (proved from the extension's purge step; the tester's `purgeRound` model performs it,
W4c).

Until C6 nothing links this model to the server's (`walRecs`, `walFiles`): the server's WAL is
described by `storage.WalRecs`, the tester's (W4c) by this (option B of Q-W4a-1).
-/
module

public import GooseLang.Ext.AbsDisk.Specs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalHist
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal.walpb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The (index, term) pairs `ValidSnapshotEntries` returns from a WAL whose history is `I` read from
position `k` on: `Create`'s `⟨0, 0⟩` if nothing is purged, then the snapshot records of `I.drop k`
at or below the history's last commit, in record order. -/
def walValidSnaps (I : WalHist) (k : Nat) : List (w64 × w64) :=
  (if k = 0 then [(W64 0, W64 0)] else []) ++
  (I.drop k).filterMap (fun o => match o with
    | .snap m => if uint.nat m.Index' ≤ uint.nat (walLastHS I).Commit' then some (m.Index', m.Term')
      else none
    | .save _ _ => none)

/-- The newest of a list of (index, term) snapshot pairs: the highest index, the last of equal ones
(bootstrap's `newestSnapshotEntry`, as `walNewest`). -/
def walNewestPair (l : List (w64 × w64)) : Option (w64 × w64) :=
  l.foldl (fun acc p => match acc with
    | none => some p
    | some q => if uint.nat q.1 ≤ uint.nat p.1 then some p else some q) none

/-- The last position of a snapshot record of index `a` in `H` (0 if none): the records before it
are in files `ReleaseLockTo(a)` (and a restart's `Open` at `a`) unlocks. -/
def walLastSnapPos {E : Type} (H : List (WalOpG E)) (a : w64) : Nat :=
  ((List.range H.length).filter (fun i => match H[i]? with
    | some (WalOpG.snap m) => decide (m.Index' = a)
    | _ => false)).getLast?.getD 0

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [go_gctx : GoGlobalContext]
  [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- **The WAL in `dir` holds the history `H`, with flag `sized`** (the extension's points-to, read
over `EntryM`): its durable state's history, as model entries, and flag; the marks, purge positions
and metadata as they are (`walDiskAt` names them). -/
def walDisk (dir : GoString) (H : WalHist) (sized : Bool := false) : IProp GF :=
  iprop(∃ d : WalDur, walDiskAt dir d ∗ ⌜d.H.map WalOpG.toM = H ∧ d.sized = sized⌝)

instance walDisk_timeless (dir : GoString) (H : WalHist) (sized : Bool) :
    Timeless (walDisk (GF := GF) dir H sized) := by
  unfold walDisk; infer_instance

/-- **`sp` points to a `walpb.Snapshot` of index `md.Index'` and term `md.Term'`, whose conf
state is non-nil iff `cs`** (persistent: the object frozen). -/
def walSnapAt (sp : Loc) (md : SnapshotMetadataM) (cs : Bool) : IProp GF :=
  iprop(∃ s : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot, sp ↦□ s ∗
    s.Index' ↦□ md.Index' ∗ s.Term' ↦□ md.Term' ∗ ⌜cs = decide (s.ConfState' ≠ null)⌝)

/-- **`sp` points to a `walpb.Snapshot` of index and term `s`** (persistent). -/
def walSnapIdTerm (sp : Loc) (s : w64 × w64) : IProp GF :=
  iprop(∃ (md : SnapshotMetadataM) (cs : Bool), walSnapAt sp md cs ∗ ⌜(md.Index', md.Term') = s⌝)

/-- **The pointers `ps` point to `walpb.Snapshot`s of indexes and terms `snaps`**, in order
(persistent). -/
def walSnapsAt (ps : List Loc) (snaps : List (w64 × w64)) : IProp GF :=
  iprop([∗list] p; s ∈ ps; snaps, walSnapIdTerm p s)

instance walSnapAt_persistent (sp : Loc) (md : SnapshotMetadataM) (cs : Bool) :
    Persistent (walSnapAt (GF := GF) sp md cs) := by unfold walSnapAt; infer_instance
instance walSnapIdTerm_persistent (sp : Loc) (s : w64 × w64) :
    Persistent (walSnapIdTerm (GF := GF) sp s) := by unfold walSnapIdTerm; infer_instance

/-- **The purge law** (the approved Draft's §1.5; proved from the extension's purge step, which the
tester's trusted `purgeRound` model performs, W4c): a purge round in `dir`, while the purge's right
is held, may delete the records before `unl` (`pur := max pur unl`). Stated over the step itself
until the tester's `purgeRound` (and its model) exist. -/
theorem walPurge_step (dir : GoString) (d : WalDur) :
    {{ walDiskAt (L := hG.goose_localGS) dir d ∗ walPurgeRight (GF := GF) dir }}
      (ExternalOp absDiskExt.name "WalPurge" (Val (#dir)))
    {{ RET #(); walDiskAt (L := hG.goose_localGS) dir { d with pur := max d.pur d.unl } ∗
        walPurgeRight dir }} := by
  iintro %Φ ⟨Hd, Hr⟩ HΦ
  iapply wp_WalPurge dir d Φ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iframe Hd
  iintro Hd %s' _ %_
  inext
  imod Hclose
  imodintro
  iapply HΦ
  iframe Hd Hr

end defs

end EtcdGrove
end Perennial
