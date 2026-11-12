/-
**The WAL's records and directory, as the server's storage writes them** (2026-11-03; the WAL API's
storage part, approved by the user: `notes/decisions.md`, "The WAL's API"; the contract over the
server's storage is `etcdserver/WalApi.lean`). Lean-first.

The model of the WAL's records (`walFresh`, `walSave`, `walSaveSnap`, `WalSaveOk`), the records
(`walRecs`) and their base's lower bounds (`walBaseLb`), a closed WAL's files (`walFiles`,
axiomatized, as a fresh directory's `dataDirFresh`, `WalDir.lean`), the purge's right (`walPurgeRight`), the WAL's directory and metadata (`walDirOf`,
`walMetaIs`, `config.walDirOf`). The ghost variables' meaning is trusted (see each docstring); the
module is sealed (`etc/import-all.txt`): no `import all` of it, so no proof updates them except
through the trusted contracts (`isWalStorage`, `bootstrap`'s, `purgeFile`'s).

What the model describes is the goosed fork's WAL (`goose-lean-walsnap`: the nonissues
`etcd-wal-stale-entries-above-snapshot`, `etcd-wal-snapshot-record-order`,
`etcd-wal-restart-file-below-snapshot`); upstream's `ReadAll`, `recoverSnapshot` and `enti` make it
false.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.raft.v3.NodeApiVocab
public import Proof.go_etcd_io.raft.v3.Protocol.CommitWit
public import Proof.go_etcd_io.raft.v3.Protocol.RaftState
public import Proof.go_etcd_io.raft.v3.PbModel
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.GhostVar
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDir

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The records' model (pure) -/

section model
variable [GooseExts]

/-- **The records of a new WAL** (`wal.Create`: the initial snapshot record at `⟨0, 0⟩`, no
entries, no hard state). -/
def walFresh : StorContents :=
  ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩

/-- **The records after `Save(h, es)`**: the hard state replaced unless `h` is empty (`phsNext`:
`saveState` skips an empty one), the entries truncate-appended (`appendEnts`: `ReadAll`'s
`append(ents[:offset], e)` for consecutive entries above the base, `WalSaveOk`). -/
def walSave (σ : StorContents) (h : HardStateM) (es : List EntryM) : StorContents :=
  { σ with hs := phsNext σ.hs h, ents := appendEnts σ.base σ.ents es }

/-- **The records after `SaveSnap(m)`**: a record below the base changes nothing (the restart
opens at the highest record); otherwise they start at `m` (its index and term, the snapshot `m`
without data: the WAL keeps the metadata), the entries above it kept when `m` is within the saved
commit (a snapshot of the applied log) and dropped when above it (a received snapshot: raft
discarded its log). The hard state kept. -/
def walSaveSnap (σ : StorContents) (m : SnapshotMetadataM) : StorContents :=
  if uint.nat m.Index' < σ.b then σ else
  { σ with
    base := entryID.mk m.Term' m.Index'
    snap := some (SnapshotM.mk [] m)
    ents := if uint.nat m.Index' ≤ σ.commit then σ.ents.drop (uint.nat m.Index' - σ.b) else [] }

/-- `Save` keeps the base. -/
theorem walSave_base (σ : StorContents) (h : HardStateM) (es : List EntryM) :
    (walSave σ h es).base = σ.base := rfl

/-- After `SaveSnap(m)` the base is at least `m`'s index (a record below it changes nothing, above
it starts the records), and at least the old base. -/
theorem walSaveSnap_base_ge (σ : StorContents) (m : SnapshotMetadataM) :
    σ.b ≤ (walSaveSnap σ m).b ∧ (uint.nat m.Index' ≤ (walSaveSnap σ m).b ∨ uint.nat m.Index' < σ.b) := by
  unfold walSaveSnap
  split
  · next h => exact ⟨Nat.le_refl _, Or.inr h⟩
  · next h =>
    simp only [StorContents.b] at h ⊢
    exact ⟨by omega, Or.inl (Nat.le_refl _)⟩

/-- **`Save`'s case the server uses**: consecutive entries above the records' base, the first at
most one past their last (else `ReadAll` fails, `ErrSliceOutOfRange`, or truncates where `walSave`
does not). Raft's `Ready` gives it (`readyRest_indices`; after a snapshot, `readySnap`'s
`LogIndicesOk`). -/
def WalSaveOk (σ : StorContents) (es : List EntryM) : Prop :=
  ∀ e0, es.head? = some e0 → σ.b < uint.nat e0.Index' ∧ uint.nat e0.Index' ≤ σ.last + 1 ∧
    ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = uint.nat e0.Index' + j

end model

/-- **The WAL directory of the configuration with data directory `dataDir` and dedicated WAL
directory `dedicated`** (opaque, as `config.backendPathOf`): `ServerConfig.WALDir()`, the dedicated
directory if set, else `datadir.ToWALDir(dataDir)` (`filepath.Join(dataDir, "member", "wal")`). -/
opaque config.walDirOf [GooseExts] (dataDir dedicated : GoString) : GoString

instance storContents_countable_api [GooseExts] : Pos.Countable StorContents :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.hs, σ.snap, σ.base, σ.ents))
    (by
      rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
      have h := Pos.encode_inj h
      simp_all)

/-! ## The tokens -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The ghost names of the WAL `w`'s records and of their base's lower bounds (opaque: one per
WAL, as `storage.walGName`; the storage's WAL identity, `storage.walOf st`). -/
opaque walRecGName (w : Loc) : GName
opaque walBaseGName (w : Loc) : GName

/-- **The WAL `w`'s records are `σ`** (sealed; exclusive, timeless; only its meaning is trusted, as
`storage.walOpen`'s): once `σ.b ≤ σ.commit`, what `ReadAll` returns when a restart opens the WAL at
its snapshot record of the highest index at or below the saved commit: the snapshot record at
`σ.base`, the last hard state `σ.hs`, the entries above `σ.base`. With the authority over its base's
lower bounds (`walBaseLb`): the base only grows.

(raft-entsize §5, [r3g], 2026-11-09; the axiom review's W2/W3) **`sized`** (default `false`, today's
meaning): when `true`, every entry record written by a *successful* `Save` (one whose law commits,
`storage.walSaveOk`) is `pbutil.MustMarshalMessage(e)` of an entry object `e` that held a content
`c` with `entSizeOk c` when it was saved (the `Save` law at `sized = true` takes those objects;
`saveEntry` marshals the saved object, `wal.go:1072-1078` at the pin `0b50f0426`, called per
entry from `Save`'s loop, `:1112`). A failed `Save` (`¬ storage.walSaveOk`: its law commits no
update, at either flag) may have written some records and leaves the flag as it was, so a failed
`Save` at `false` into a sized WAL may leave unbounded records under `true`: a future `ReadAll` law
that gives the bound must take `walSaveOk` (`diskOk`). `wal.Create` starts with no entry records,
so `bootstrap`'s first start gives `true` (`wal.bootOk`). `SaveSnap` only drops entries, so it keeps
the flag. `false` claims nothing of the records' contents, so `true` weakens to it
(`walRecs_unsize`). The flag is in the records' ghost variable, so every `Save`, `SaveSnap` and
`Close` of the WAL sees the same flag (whichever storage over `w` they go through). -/
@[no_expose] def walRecs (w : Loc) (σ : StorContents) (sized : Bool := false) : IProp GF :=
  iprop(ghostVar (walRecGName w) 1 (σ, sized) ∗ monoNatAuthOwn (walBaseGName w) 1 σ.b)

/-- **The WAL `w`'s records' base is at least `i`** (persistent). -/
@[no_expose] def walBaseLb (w : Loc) (i : Nat) : IProp GF := monoNatLbOwn (walBaseGName w) i

instance walRecs_timeless (w : Loc) (σ : StorContents) (sized : Bool) :
    Timeless (walRecs (GF := GF) w σ sized) := by
  unfold walRecs; infer_instance

/-- (raft-entsize §5, [r3g]) **A sized WAL's records are also unsized ones**: `sized = false`
claims nothing of the records' contents. -/
theorem walRecs_unsize (w : Loc) (σ : StorContents) (sized : Bool) :
    walRecs (GF := GF) w σ sized ⊢ |==> walRecs w σ false := by
  unfold walRecs
  iintro ⟨Hv, Ha⟩
  imod ghostVar_update (σ, false) (walRecGName w) (σ, sized) $$ Hv with Hv
  imodintro
  iframe Hv Ha

instance walBaseLb_persistent (w : Loc) (i : Nat) : Persistent (walBaseLb (GF := GF) w i) := by
  unfold walBaseLb; infer_instance

instance walBaseLb_timeless (w : Loc) (i : Nat) : Timeless (walBaseLb (GF := GF) w i) := by
  unfold walBaseLb; infer_instance

/-- Two records of one WAL exclude each other. -/
theorem walRecs_excl (w : Loc) (σ σ' : StorContents) (s : Bool := false) (s' : Bool := false) :
    walRecs (GF := GF) w σ s ∗ walRecs w σ' s' ⊢ False := by
  unfold walRecs
  iintro ⟨⟨-, A1⟩, ⟨-, A2⟩⟩
  iapply monoNatAuthOwn_exclusive (walBaseGName w) σ.b σ'.b $$ A1 A2

/-- The records' base is a lower bound of itself. -/
theorem walRecs_baseLb (w : Loc) (σ : StorContents) (sized : Bool := false) :
    walRecs (GF := GF) w σ sized ⊢ walRecs w σ sized ∗ walBaseLb w σ.b := by
  unfold walRecs walBaseLb
  iintro ⟨Hv, Ha⟩
  ihave #Hl := monoNatLbOwn_get (walBaseGName w) 1 σ.b $$ Ha
  isplitl [Hv Ha]
  · iframe
  · iexact Hl

/-- Lower bounds of the base weaken. -/
theorem walBaseLb_mono (w : Loc) (i j : Nat) (h : j ≤ i) :
    walBaseLb (GF := GF) w i ⊢ walBaseLb w j := by
  unfold walBaseLb
  iintro H
  iapply (monoNatLbOwn_le (γ := walBaseGName w) j h) $$ H

/-- (Sweep repairs 1, W2) **After `SaveSnap(m)`, the records start at or above `m`'s index**: a lower
bound of the base at `m`'s index (what `storage.Release` at `m` takes). -/
theorem walRecs_saveSnap_baseLb (w : Loc) (σ : StorContents) (m : SnapshotMetadataM)
    (sized : Bool := false) :
    walRecs (GF := GF) w (walSaveSnap σ m) sized ⊢
      walRecs w (walSaveSnap σ m) sized ∗ walBaseLb w (uint.nat m.Index') := by
  iintro Hr
  icases walRecs_baseLb w _ sized $$ Hr with ⟨Hr, #Hl⟩
  iframe Hr
  iapply walBaseLb_mono w _ _ ?_ $$ Hl
  obtain ⟨h1, h2⟩ := walSaveSnap_base_ge σ m
  omega

/-- A lower bound of the base is below the records' base. -/
theorem walRecs_baseLb_le (w : Loc) (σ : StorContents) (i : Nat) (sized : Bool := false) :
    walRecs (GF := GF) w σ sized ∗ walBaseLb w i ⊢ walRecs w σ sized ∗ ⌜i ≤ σ.b⌝ := by
  unfold walRecs walBaseLb
  iintro ⟨⟨Hv, Ha⟩, #Hl⟩
  icases monoNatLbOwn_valid (walBaseGName w) 1 σ.b i $$ Ha Hl with %H
  iframe
  ipureintro; exact H.2

/-- **The WAL `w`'s directory** (opaque; `w.dir`). -/
opaque walDirOf (w : Loc) : GoString

/-- **The files of a closed WAL in the directory `dir` hold the records `σ`, its metadata the
member `id` of the cluster `cid`** (axiomatized, timeless; a trust-boundary token, as `dataDirFresh`,
`WalDir.lean`: the user's choice, 2026-11-03): `wal.Open(dir, s)` at the snapshot record
`recoverSnapshot` picks (the highest valid one), then `ReadAll`, returns `σ` and the metadata.
Made by `Close`; consumed by a restart's `bootstrap` (its contract). A graceful stop in one
process. No axiom says it is exclusive: read as `True`, every axiom about it holds.

(raft-entsize §5, [r3g], 2026-11-09; the axiom review's W2/W3) **`sized`** (default `false`, today's
meaning): when `true`, every entry record in the files written by a *successful* `Save`
(`storage.walSaveOk`) is `pbutil.MustMarshalMessage(e)` of a saved entry object whose content `c`
had `entSizeOk c` (`walRecs`'s `sized`, which `Close` carries into the files: `Close` syncs and
closes, it writes no record; `saveEntry`, `wal.go:1072-1078` at the pin `0b50f0426`, from
`Save`'s loop, `:1112`). A failed `Save` leaves the flag as it was, possibly with records it
wrote (a failed `Save` at `false` into a sized WAL may leave unbounded records under `true`).
`ReadAll` decodes each entry record with `Unmarshal` (`wal.go:525-526`, `decoder.go:215-218`), whose exact round trip (stage A's `D2`,
`proto/UnmarshalPb.lean`) gives back the saved content, unknown fields included, so the replayed
entries are `entSizeOk`: `bootstrapRestartContract` states it (out_size C3), under its premise
`storage.walSaveOk` (no `Save` failed), as `bootOkR`'s `Hγsz` (the replayed storage sized:
`InvRestart.lean`). A WAL written by another program is at `false`: today's facts only. -/
axiom walFiles {GF : BundledGFunctors} [GooseExts] (dir : GoString) (id cid : w64)
    (σ : StorContents) (sized : Bool := false) : IProp GF

axiom walFiles_timeless {GF : BundledGFunctors} [GooseExts] (dir : GoString) (id cid : w64)
    (σ : StorContents) (sized : Bool := false) : Timeless (walFiles (GF := GF) dir id cid σ sized)

attribute [instance] walFiles_timeless

/-- **The right to close the WAL in the directory `dir` with its files kept** (opaque, exclusive;
trust boundary): the server's purge of old WAL files there (`purgeFile`, which removes the
oldest files no lock holds) is not running. `Close` releases every lock, so the files a restart
reads survive only if the purge has stopped; etcd's stop order gives it (`s.wg.Wait()`, which
waits for `purgeFile`, before `s.r.stop()`). `bootstrap`'s contract gives it, `purgeFile` takes it
and gives it back when it returns. -/
opaque walPurgeRight (dir : GoString) : IProp GF

/-- The trust-boundary fact under `walMetaIs` (opaque). -/
opaque walMetaRaw (w : Loc) (id cid : w64) : IProp GF

/-- **The WAL `w`'s metadata names the member `id` of the cluster `cid`** (persistent; trust
boundary): `wal.Create(dir, Metadata{NodeID: id, ClusterID: cid})`'s, which `ReadAll` checks
against every metadata record. -/
def walMetaIs (w : Loc) (id cid : w64) : IProp GF := iprop(□ walMetaRaw w id cid)

instance walMetaIs_persistent (w : Loc) (id cid : w64) :
    Persistent (walMetaIs (GF := GF) w id cid) := by
  unfold walMetaIs; infer_instance

end defs

end EtcdGrove
end Perennial
