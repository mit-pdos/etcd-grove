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
public import GooseLang.Ext.Durable.Specs
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

/-- **Every file a cut names after `H`'s last snapshot record of index `a` (position `p`) is named
above `a`** (a sufficient condition, by the Go code; M1 of the Freeze review): every saved commit
from `p` on is at least `a` (so `a` is a valid snapshot of every image holding `p`, and a restart
starts at or above it); every entry record after a snapshot record of index `≥ a` has index `> a`;
every snapshot record after `p` has index `≥ a`. Then `w.enti ≥ a` at every cut after `p`, across
restarts (`SaveSnapshot` and `ReadAll` raise it to the snapshot's index, S/wal.go:1158, :578), and
the file names (`enti + 1`) exceed `a`. -/
def walRelGuard (H : WalHist) (a : w64) (p : Nat) : Prop :=
  (∀ j, p < j → j ≤ H.length → uint.nat a ≤ uint.nat (walLastHS (H.take j)).Commit') ∧
  (∀ (q j : Nat) (m : SnapshotMetadataM) (h : HardStateM) (es : List EntryM) (e : EntryM),
     H[q]? = some (WalOpG.snap m) → uint.nat a ≤ uint.nat m.Index' → q < j →
     H[j]? = some (WalOpG.save h es) → e ∈ es → uint.nat a < uint.nat e.Index') ∧
  (∀ (j : Nat) (m : SnapshotMetadataM), p < j → H[j]? = some (WalOpG.snap m) → uint.nat a ≤ uint.nat m.Index')

open Classical in
/-- **A position before which `ReleaseLockTo(a)` / a restart's `Open` at `a` leaves records
unlocked, and from which every record stays locked**: 0 for `a = 0` (file 0 is named 0, every later
file higher); the last snapshot record of index `a` under `walRelGuard`; otherwise the history's
length (the tail file is never released). -/
def walReleasePos (H : WalHist) (a : w64) : Nat :=
  if a = W64 0 then 0
  else if (∃ (i : Nat) (m : SnapshotMetadataM), H[i]? = some (WalOpG.snap m) ∧ m.Index' = a) ∧ walRelGuard H a (walLastSnapPos H a)
    then walLastSnapPos H a else H.length

/-! The empty `Save` (S/wal.go:1079: an empty state and no entries write nothing; the model appends
`save hsZero []`): no reader sees it. -/

theorem walFoldChkFrom_phantom (σ : StorContents) (H₁ H₂ : WalHist) :
    walFoldChkFrom σ (H₁ ++ WalOpG.save hsZero [] :: H₂) = walFoldChkFrom σ (H₁ ++ H₂) := by
  induction H₁ generalizing σ with
  | nil =>
    simp only [List.nil_append, walFoldChkFrom, List.foldlM_nil, phsNext_empty _ hsZero ⟨rfl, rfl, rfl⟩]
    rfl
  | cons o H ih =>
    cases o with
    | snap m => simp only [List.cons_append, walFoldChkFrom]; exact ih _
    | save h es => simp only [List.cons_append, walFoldChkFrom, ih]

theorem walLastHS_phantom (H₁ H₂ : WalHist) :
    walLastHS (H₁ ++ WalOpG.save hsZero [] :: H₂) = walLastHS (H₁ ++ H₂) := by
  simp only [walLastHS, List.foldl_append, List.foldl_cons, phsNext_empty _ hsZero ⟨rfl, rfl, rfl⟩]

theorem walRead_phantom (H₁ H₂ : WalHist) :
    walRead (H₁ ++ WalOpG.save hsZero [] :: H₂) = walRead (H₁ ++ H₂) := by
  simp only [walRead, walLastHS_phantom, List.filter_append, List.filter_cons, walKeep, if_true,
    walFoldChkFrom_phantom]

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [go_gctx : GoGlobalContext]
  [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

open Classical in
/-- **No durable name lies under the WAL area `r`**: durable's reservation of `r`, when the program
has the durable extension. -/
def durableResvD (r : GoString) : IProp GF :=
  if h : HasExt durableExt then (haveI := h; durableReserved (L := hG.goose_localGS) r)
  else iprop(True)

instance durableResvD_persistent (r : GoString) : Persistent (durableResvD (GF := GF) r) := by
  unfold durableResvD; split <;> infer_instance

/-- **The WAL area is `r`, and the durable extension's names stay out of the WAL's footprint**:
absDisk's area, and durable's reservation of it when the program has the durable extension (every
WAL function that takes a directory, and `TouchDirAll`, require it). No other path user is
constrained (`Impl.lean`, "What this covers"). -/
def walAreaOk (r : GoString) : IProp GF :=
  iprop(walArea (L := hG.goose_localGS) r ∗ durableResvD r)

instance walAreaOk_persistent (r : GoString) : Persistent (walAreaOk (GF := GF) r) := by
  unfold walAreaOk; infer_instance

/-- **The WAL in `dir` holds the history `H`, with flag `sized`** (the extension's points-to, read
over `EntryM`): its durable state's history, as model entries, and flag; the purge positions and
metadata as they are, the mark and `named` as lower bounds (`walDiskAt`). -/
def walDisk (dir : GoString) (H : WalHist) (sized : Bool) : IProp GF :=
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
on the open WAL `w` is held (`walPurgeW`, one per handle, per generation), may delete the records before `unl` (`pur := max pur unl`), and moves the read position to the
start `k` of the first file it left (`cut ≤ k ≤ max pur unl`). Stated over the step itself
until the tester's `purgeRound` (and its model) exist. The right is framed here; the step itself
(`wp_WalPurge`) needs none, so the right constrains only through its consumers. **W4c gate**
(revision round 3, M1; `notes/decisions.md`): `purgeRound`'s spec takes `walPurgeW w dir` and
`walOpenW w dir`, consumed or framed, never derived; with them `unl` is current (raised by `Open`,
`ReleaseLockTo`) and at most one handle, so one right, is live (the lock token). -/
theorem walPurge_step (w : Loc) (dir : GoString) (d : WalDur) (k : Nat) (hk : d.cut ≤ k)
    (hk' : k ≤ max d.pur d.unl) :
    {{ walDiskAt (L := hG.goose_localGS) dir d ∗ walPurgeW (L := hG.goose_localGS) w dir }}
      (ExternalOp absDiskExt.name "WalPurge" (Val (PairV (#dir) (#(walCode k)))))
    {{ RET #(); walDiskAt (L := hG.goose_localGS) dir { d with pur := max d.pur d.unl, cut := k } ∗
        walPurgeW (L := hG.goose_localGS) w dir }} := by
  iintro %Φ ⟨Hd, Hr⟩ HΦ
  iapply wp_WalPurge dir k d ⟨hk, hk'⟩ Φ
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
