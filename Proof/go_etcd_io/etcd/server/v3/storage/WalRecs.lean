/-
**The WAL's records and directory, as the server's storage writes them** (2026-11-03; the WAL API's
storage part, approved by the user: `notes/decisions.md`, "The WAL's API"; the contract over the
server's storage is `etcdserver/WalApi.lean`). Lean-first.

The model of the WAL's records (`walFresh`, `walSave`, `walSaveSnap`, `WalSaveOk`), and (wal-link L3,
2026-11-18, `notes/wal-link-l3-statements.md`) the server's WAL vocabulary defined over the real WAL
(layer 1, `Proof/.../storage/wal/`) through the record `WalH` of an open WAL: its share (`storage.walOpen`),
records (`walRecs`), their base's lower bounds (`walBaseLb`), a synced snapshot record (`walSnapRec`), a
closed WAL's files (`walFiles`, over `WalA`), the purge's right (`walPurgeRight`) and the metadata
(`walMetaIs`). Until L3 these were trusted tokens over opaque ghost names and an axiom (`walFiles`). The
module is sealed (`etc/import-all.txt`).

What the model describes is the goosed fork's WAL (`goose-lean-walfs3-fp`: the nonissues
`etcd-wal-stale-entries-above-snapshot`, `etcd-wal-snapshot-record-order`,
`etcd-wal-restart-file-below-snapshot`; fixes 0001-0008, `notes/wal-fsext-fork/README.md`).
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
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsCore
public import Proof.go_etcd_io.etcd.server.v3.storage.WalLinkPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Codec
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Srv
public import Perennial.Ghost.MonoList
public import GooseLang.Ext.Fs.PathFitsLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The records' model (pure) -/

section model
variable [GooseExts]

/-- **The records after `Save(h, es)`**: the hard state replaced unless `h` is empty (`phsNext`:
`saveState` skips an empty one), the entries truncate-appended (`appendEnts`: `ReadAll`'s
`append(ents[:offset], e)` for consecutive entries above the base, `WalSaveOk`). -/
def walSave (σ : StorContents) (h : HardStateM) (es : List EntryM) : StorContents :=
  { σ with hs := phsNext σ.hs h, ents := appendEnts σ.base σ.ents es }

/-- `Save` keeps the base. -/
theorem walSave_base (σ : StorContents) (h : HardStateM) (es : List EntryM) :
    (walSave σ h es).base = σ.base := rfl

/-- **`Save`'s case the server uses**: consecutive entries above the records' base, the first at
most one past their last (else `ReadAll` fails, `ErrSliceOutOfRange`, or truncates where `walSave`
does not). Raft's `Ready` gives it (`readyRest_indices`; after a snapshot, `readySnap`'s
`LogIndicesOk`). -/
def WalSaveOk (σ : StorContents) (es : List EntryM) : Prop :=
  ∀ e0, es.head? = some e0 → σ.b < uint.nat e0.Index' ∧ uint.nat e0.Index' ≤ σ.last + 1 ∧
    ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = uint.nat e0.Index' + j

end model

-- (wal-link P2, 2026-11-19) the opaque `config.walDirOf dataDir dedicated` (`ServerConfig.WALDir()`) is
-- gone: every configuration the contracts cover has the dedicated WAL directory `srvWalDirOf dataDir`
-- (`WalLayout.lean`), which `WALDir()` returns.

instance storContents_countable_api [GooseExts] : Pos.Countable StorContents :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.hs, σ.snap, σ.base, σ.ents))
    (by
      rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
      have h := Pos.encode_inj h
      simp_all)

/-! ## The server's WAL over layer 1 (wal-link L3, `notes/wal-link-scope.md` §3.1-§3.5)

Until L3 the records, their base's lower bounds, a closed WAL's files, the purge's right, the WAL's
directory and metadata were trusted tokens over opaque ghost names (`walRecGName`, `walBaseGName`,
`walDirOf`, `walMetaRaw`, the axiom `walFiles`). They are now defined over the real WAL's resources
(layer 1: `WalFs.walDiskAt`, the shared handle `walOpenWS`, `WalFs.walPurgeW`, ...) through the record
`WalH` of what names one open WAL: the file system's instances, the WAL ghost state `W`, the I/O-error
set `Sio` the run is restricted by (with every inode in it, `cov`: the closed theorems' `NoIoErr`
premise, `notes/wal-link-scope.md` Q3), the area `r` under the roots `R` (`walAreaOk`), the directory
`dir`, the `*wal.WAL` `w`, the shared handle's ghost names `γ`, the metadata bytes `md`, and the ghost
name `γh` of the history's prefixes (`walSnapRec`, `walBaseLb`). The server's message model is
`walSrvP`/`walSrvMr` (`RaftModel/Srv.lean`): the history holds wrapped entries (`walEntW`), the server's
records are the checked fold of the unwrapped history (`walSrvHist`). -/

/-- **The WAL's history as the server reads it**: the entries' wraps unwrapped (`walEntUnwrap`). -/
def walSrvHist [GooseExts] (H : List (WalOpG WalEnt)) : WalHist :=
  (H.map WalOpG.toM).map (walOpMapE walEntUnwrap)

/-- **Every entry record of the history is the wrap of a content of bounded size** (`walRecs`' `sized`). -/
def walEntsSized [GooseExts] (H : List (WalOpG WalEnt)) : Prop :=
  ∀ (hs : HardStateM) (es : List EntryM), WalOpG.save hs es ∈ H.map WalOpG.toM →
    ∀ e ∈ es, ∃ c : EntryC, e = walEntW c ∧ entSizeOk c

/-- **The metadata bytes of the member `id` of the cluster `cid`**: protobuf-go's encoding of
`&etcdserverpb.Metadata{NodeID: &id, ClusterID: &cid}` (`bootstrap.go:712-715`: both fields set, so both
written, in field order). -/
def walMetaEnc [GooseExts] (id cid : w64) : List w8 :=
  WalEnc.optVarintField 1 (some (uint.nat id)) ++ WalEnc.optVarintField 2 (some (uint.nat cid))

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A WAL area and directory** (see the section header): what a closed WAL's files are named by.
(wal-fsfix2, 2026-11-20, approved by the user via etcd-grove-03: ledger "`cut.specNoErr` needs lock
coverage and a WAL directory that fits") Every step also satisfies `NoMapLockErr Sio` (`satL`: the lock
calls on the covered files succeed whenever they can, as `NoIoErr` for the other calls; `fileutil.LockFile`
takes `flock` when `init` finds no OFD locks), and the WAL directory fits (`fits`, `Fs.DirFits`: the paths
`cut` makes below it, `dir/<seq>-<index>.wal` and `dir/<n>.tmp`, fit, which `NoIoErr` asks of a path call
it covers) and every path below it (`child dir b`, `b` possibly with `/`) is in `Sio` by path (`covP`, approved by the user 2026-11-20: ledger, "`cut.specNoErr`
also needs the WAL directory's paths covered"; `cov` covers inodes only, and `NoIoErr` covers a path call only on a
path in `Sio`). The closed theorems allocate the area with all three (`lib/etcdstart/WalAreas.lean`:
`etcdSQ`'s second half, and the member's name of at most 200 bytes). -/
structure WalA (GF : BundledGFunctors) where
  ext : ExtSemantics Fs.fsExt
  semOk : Fs.FsSemOk (S := ext)
  has : HasExt Fs.fsExt
  W : WalFs.WalGS GF
  Sio : Fs.IoSet
  sat : Fs.FsStepSat (Fs.NoIoErr Sio) (S := ext)
  satL : Fs.FsStepSat (Fs.NoMapLockErr Sio) (S := ext)
  cov : WalFs.walCov Sio
  R : Fs.Roots
  jr : Fs.Ino
  r : GoString
  dir : GoString
  fits : Fs.DirFits dir
  covP : ∀ b, Sio.path (Fs.child dir b)

/-- **An open WAL** (see the section header). -/
structure WalH (GF : BundledGFunctors) extends WalA GF where
  inj : go.BasicIntoValInj
  w : Loc
  γ : WalFs.WalShN
  md : List w8
  γh : GName

section walOpen
variable [wal_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **A share `q` of the open WAL `h`** (persistent area facts, the shared handle's share, the handle's
persistent length bound at `0`, which layer 1's `Sync` takes): every share
lets the storages over `h.w` write it (`Save`, `SaveSnap`, `Sync`, `Release`), the whole closes it
(`Close`). Until L3 a ghost variable over the opaque `walGName w`. -/
def storage.walOpen (h : WalH GF) (q : Qp) : IProp GF :=
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj
  iprop(WalFs.walOpenWS h.Sio walSrvP walSrvMr h.w h.dir h.γ q ∗
    WalFs.walAreaOk walCodec walSrvMr h.R h.jr h.r ∗ WalFs.walLenLb h.w h.dir h.γ.inc 0)

/-- The shares of an open WAL are fractional. -/
instance storage.walOpen_fractional (h : WalH GF) :
    Fractional (fun q => storage.walOpen (GF := GF) h q) where
  fractional q1 q2 := by
    letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj
    unfold storage.walOpen
    have hs := WalFs.walOpenWS_split (GF := GF) (hG := hG) h.Sio walSrvP walSrvMr h.w h.dir h.γ q1 q2
    constructor
    · iintro ⟨H, #Ha, #Hl⟩
      icases hs.1 $$ H with ⟨H1, H2⟩
      iframe H1 H2 Ha Hl
    · iintro ⟨⟨H1, #Ha, #Hl⟩, ⟨H2, -, -⟩⟩
      ihave H := hs.2 $$ [H1 H2]
      · iframe H1 H2
      iframe H Ha Hl

instance storage.walOpen_as_fractional (h : WalH GF) (q : Qp) :
    AsFractional (storage.walOpen (GF := GF) h q) ioΦ (fun q => storage.walOpen h q) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := storage.walOpen_fractional h

end walOpen

/-- **The WAL `h`'s records are `σ`** (sealed; exclusive, timeless): the WAL's durable state `d`
(`WalFs.walDiskAt`), whose history folds, unwrapped, to `σ` (`walFoldChkFrom walFresh`, the eager model
`walSave`/`walSaveSnap` step by step), its metadata `h.md`, layer 1's flag `d.sized` set (no step
clears it, `walDurFresh` sets it: what layer 1's `Save`/`SaveSnapshot` updates read), its name durable (`walNamed`), with the
authority over the history's prefixes (`walSnapRec`, `walBaseLb`). Once `σ.b ≤ σ.commit`, what a restart
reads (`walRead_of_fold`). **`sized`**: every entry record is the wrap of a content `c` with
`entSizeOk c` (`walEntsSized`); `false` claims nothing more. -/
@[no_expose] def walRecs (h : WalH GF) (σ : StorContents) (sized : Bool := false) : IProp GF :=
  letI := h.W
  iprop(∃ d : WalDur, WalFs.walDiskAtI h.dir h.γ.inc d ∗ monoListAuthOwn h.γh 1 d.H ∗ WalFs.walNamed h.dir h.γ.inc ∗
    ⌜walFoldChkFrom walFresh (walSrvHist d.H) = some σ ∧ d.metadata = h.md ∧ d.sized = true ∧
      (sized = true → walEntsSized d.H)⌝)

/-- **The WAL `h`'s records' base is at least `i`** (persistent): a prefix of the history folds to records
of base at least `i`. -/
@[no_expose] def walBaseLb (h : WalH GF) (i : Nat) : IProp GF :=
  iprop(∃ H0 : List (WalOpG WalEnt), monoListLbOwn h.γh H0 ∗
    ⌜∃ σ0 : StorContents, walFoldChkFrom walFresh (walSrvHist H0) = some σ0 ∧ i ≤ σ0.b⌝)

/-- **Position `i` of the WAL `h`'s history is the snapshot record `m`, synced** (persistent): what
`Release` at `m`'s index takes (`WAL.ReleaseLockTo`'s premise; made by `SaveSnap`'s law). -/
@[no_expose] def walSnapRec (h : WalH GF) (i : Nat) (m : SnapshotMetadataM) : IProp GF :=
  letI := h.W
  iprop(∃ H0 : List (WalOpG WalEnt), monoListLbOwn h.γh H0 ∗ WalFs.walSyncedLb h.dir h.γ.inc (i + 1) ∗
    ⌜∃ al, H0[i]? = some (WalOpG.snap m al)⌝)

/-- **The files of the closed WAL in the area and directory `a` hold the records `σ`, its metadata the
member `id` of the cluster `cid`** (exclusive, timeless): the durable state `d` all synced, its name
durable, the generation's lock free (`walUnlockedTok`) and the call permission's half of the directory's
root back (what `WAL.Close` returns), what a restart reads from it `σ` (`walRead`), its metadata
`walMetaEnc id cid`; `sized` as `walRecs`'. Until L3 an axiom (with `walFiles_timeless`).
(walfiles-fold, 2026-11-28) **`σ` is also the history's eager fold** (`walFoldChkFrom walFresh`, every snapshot
record applied, as `walRecs`): the files a graceful `Close` leaves (`walRecs_closeAU`). Without it the files
admitted a history ending with a synced snapshot record above the saved commit, which `walRead` drops and the
eager fold applies, so the restart contract (`bootstrapRestartContract`, whose post is `walRecs h σ`) was false
of them; etcd's graceful runs never write it (`notes/axiom-review/bootstrap-restart-eagerfold.md`).
**Describes only a cleanly closed WAL: produced only by `walRecs_closeAU`.** A crash-restart axiom or spec must
use the crash model's read-based post (`walRead`), never `walFiles`. Counterexample: `SaveSnap` synced, process
killed before `Save`; `ReadAll` skips the trailing snapshot record while the eager fold applies it
(`examples/axiomcx/restarteagerfold`). -/
@[no_expose] def walFiles (a : WalA GF) (id cid : w64) (σ : StorContents) (sized : Bool := false) :
    IProp GF :=
  letI := a.ext; letI := a.semOk; letI := a.has; letI := a.W
  iprop(∃ (i : Nat) (d : WalDur), WalFs.walDiskAtI a.dir i d ∗ WalFs.walSyncedLb a.dir i d.H.length ∗
    WalFs.walNamed a.dir i ∗
    WalFs.walUnlockedTok ∗ Fs.osCallPerm (Fs.callKey a.R a.dir) (1 : Qp).half ∗
    ⌜walRead (walSrvHist d.H) = some σ ∧ walFoldChkFrom walFresh (walSrvHist d.H) = some σ ∧
      d.metadata = walMetaEnc id cid ∧ d.sized = true ∧
      (sized = true → walEntsSized d.H)⌝)

/-- **The right to close the WAL `h` with its files kept** (exclusive): layer 1's purge right
(`WalFs.walPurgeW`): no purge of the WAL's files is running. -/
def walPurgeRight (h : WalH GF) : IProp GF :=
  letI := h.W
  WalFs.walPurgeW h.w h.dir

/-- **The WAL `h`'s metadata names the member `id` of the cluster `cid`** (pure, hence persistent). -/
def walMetaIs (h : WalH GF) (id cid : w64) : IProp GF := iprop(⌜h.md = walMetaEnc id cid⌝)

instance walMetaIs_persistent (h : WalH GF) (id cid : w64) :
    Persistent (walMetaIs (GF := GF) h id cid) := by
  unfold walMetaIs; infer_instance

instance walRecs_timeless (h : WalH GF) (σ : StorContents) (sized : Bool) :
    Timeless (walRecs (GF := GF) h σ sized) := by
  unfold walRecs; infer_instance

instance walBaseLb_persistent (h : WalH GF) (i : Nat) : Persistent (walBaseLb (GF := GF) h i) := by
  unfold walBaseLb; infer_instance

instance walBaseLb_timeless (h : WalH GF) (i : Nat) : Timeless (walBaseLb (GF := GF) h i) := by
  unfold walBaseLb; infer_instance

instance walSnapRec_persistent (h : WalH GF) (i : Nat) (m : SnapshotMetadataM) :
    Persistent (walSnapRec (GF := GF) h i m) := by
  unfold walSnapRec; infer_instance

instance walFiles_timeless (a : WalA GF) (id cid : w64) (σ : StorContents) (sized : Bool) :
    Timeless (walFiles (GF := GF) a id cid σ sized) := by
  unfold walFiles; infer_instance

/-- A sized WAL's records are also unsized ones. -/
theorem walRecs_unsize (h : WalH GF) (σ : StorContents) (sized : Bool) :
    walRecs (GF := GF) h σ sized ⊢ |==> walRecs h σ false := by
  unfold walRecs
  iintro ⟨%d, Hd, Ha, Hn, %hf⟩
  imodintro
  iexists d
  iframe Hd Ha Hn
  ipureintro; exact ⟨hf.1, hf.2.1, hf.2.2.1, fun h => by cases h⟩

/-- Two records of one WAL exclude each other. -/
theorem walRecs_excl (h : WalH GF) (σ σ' : StorContents) (s : Bool := false) (s' : Bool := false) :
    walRecs (GF := GF) h σ s ∗ walRecs h σ' s' ⊢ False := by
  unfold walRecs
  iintro ⟨⟨%d, -, A1, -⟩, ⟨%d', -, A2, -⟩⟩
  iapply monoListAuthOwn_exclusive h.γh d.H d'.H $$ A1 A2

/-- The take of the server's view of a history at a prefix's length is the prefix's view. -/
theorem walSrvHist_take {H0 H : List (WalOpG WalEnt)} (hp : H0 <+: H) :
    (walSrvHist H).take H0.length = walSrvHist H0 := by
  obtain ⟨t, rfl⟩ := hp
  unfold walSrvHist
  simp only [List.map_append]
  rw [List.take_left']
  simp

/-- A prefix's fold has a base below the whole fold's. -/
theorem walFold_prefix_b {H0 H : List (WalOpG WalEnt)} {σ0 σ : StorContents} (hp : H0 <+: H)
    (h0 : walFoldChkFrom walFresh (walSrvHist H0) = some σ0)
    (h : walFoldChkFrom walFresh (walSrvHist H) = some σ) : σ0.b ≤ σ.b := by
  obtain ⟨τ', hτ, hd⟩ := walFoldChkFrom_prefix H0.length h
  rw [walSrvHist_take hp, h0] at hτ
  cases hτ
  exact walFoldChkFrom_b_ge hd

/-- The records' base is a lower bound of itself. -/
theorem walRecs_baseLb (h : WalH GF) (σ : StorContents) (sized : Bool := false) :
    walRecs (GF := GF) h σ sized ⊢ walRecs h σ sized ∗ walBaseLb h σ.b := by
  unfold walRecs walBaseLb
  iintro ⟨%d, Hd, Ha, Hn, %hf⟩
  ihave #Hl := monoListLbOwn_get h.γh 1 d.H $$ Ha
  isplitl [Hd Ha Hn]
  · iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf
  · iexists d.H
    iframe Hl
    ipureintro; exact ⟨σ, hf.1, Nat.le_refl _⟩

/-- Lower bounds of the base weaken. -/
theorem walBaseLb_mono (h : WalH GF) (i j : Nat) (hji : j ≤ i) :
    walBaseLb (GF := GF) h i ⊢ walBaseLb h j := by
  unfold walBaseLb
  iintro ⟨%H0, #Hl, %hf⟩
  obtain ⟨σ0, h0, hi⟩ := hf
  iexists H0
  iframe Hl
  ipureintro; exact ⟨σ0, h0, Nat.le_trans hji hi⟩

/-- **After `SaveSnap(m)`, the records start at or above `m`'s index.** -/
theorem walRecs_saveSnap_baseLb (h : WalH GF) (σ : StorContents) (m : SnapshotMetadataM)
    (sized : Bool := false) :
    walRecs (GF := GF) h (walSaveSnap σ m) sized ⊢
      walRecs h (walSaveSnap σ m) sized ∗ walBaseLb h (uint.nat m.Index') := by
  iintro Hr
  icases walRecs_baseLb h _ sized $$ Hr with ⟨Hr, #Hl⟩
  iframe Hr
  iapply walBaseLb_mono h _ _ ?_ $$ Hl
  obtain ⟨h1, h2⟩ := walSaveSnap_base_ge σ m
  omega

/-- A lower bound of the base is below the records' base. -/
theorem walRecs_baseLb_le (h : WalH GF) (σ : StorContents) (i : Nat) (sized : Bool := false) :
    walRecs (GF := GF) h σ sized ∗ walBaseLb h i ⊢ walRecs h σ sized ∗ ⌜i ≤ σ.b⌝ := by
  unfold walRecs walBaseLb
  iintro ⟨⟨%d, Hd, Ha, Hn, %hf⟩, ⟨%H0, #Hl, %h0⟩⟩
  obtain ⟨σ0, hσ0, hi⟩ := h0
  ihave %hv := mono_list_auth_lb_valid h.γh 1 d.H H0 $$ Ha Hl
  isplitl [Hd Ha Hn]
  · iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf
  · ipureintro
    exact Nat.le_trans hi (walFold_prefix_b hv.2 hσ0 hf.1)

/-! ## The records' updates as layer 1's (wal-link L3: the storage's laws, `etcdserver/RnNewStorage.lean`) -/

/-- The server's view of a history after a `save` record of wrapped contents: the contents' models. -/
theorem walSrvHist_snoc_save (H : List (WalOpG WalEnt)) (hs : HardStateM) (cs : List EntryC)
    (hc : ∀ c ∈ cs, ufWire entrySchema c.uf ∧ entrySize c < 2 ^ 48) :
    walSrvHist (H ++ [(WalOpG.save hs (cs.map walEntW)).toRaw]) =
      walSrvHist H ++ [WalOpG.save hs (cs.map EntryC.model)] := by
  unfold walSrvHist
  rw [List.map_append, List.map_append, List.map_singleton, List.map_singleton, WalOpG.toM_toRaw]
  congr 2
  simp only [walOpMapE, List.map_map]
  congr 1
  exact List.map_congr_left (fun c hcm => walEntUnwrap_W (hc c hcm).1 (hc c hcm).2)

/-- The server's view of a history after a snapshot record. -/
theorem walSrvHist_snoc_snap (H : List (WalOpG WalEnt)) (m : SnapshotMetadataM) (al : Bool) :
    walSrvHist (H ++ [WalOpG.snap m al]) = walSrvHist H ++ [WalOpG.snap m al] := by
  unfold walSrvHist
  rw [List.map_append, List.map_append]
  rfl

/-- **`Save`'s update of the records as layer 1's update of the WAL's durable state** (the entries
written as their wraps `walEntW c`). -/
theorem walRecs_saveAU (h : WalH GF) (sized : Bool) (hs : HardStateM) (cs : List EntryC) (Q : IProp GF)
    (hc : ∀ c ∈ cs, ufWire entrySchema c.uf ∧ entrySize c < 2 ^ 48 ∧ (sized = true → entSizeOk c)) :
    (AU <{ ∃∃ (σ : StorContents), walRecs h σ sized ∗ ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
        @ WalFs.walAuMask, ∅ <{ walRecs h (walSave σ hs (cs.map EntryC.model)) sized, COMM Q }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d ∗ ⌜d.sized = true⌝ }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc { d with H := d.H ++ [(WalOpG.save hs (cs.map walEntW)).toRaw] },
          COMM Q }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, ⟨Hr, %hok⟩, Hcl⟩
  unfold walRecs
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplitr
  · ipureintro; exact hf.2.2.1
  isplit
  · iintro ⟨Hd, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    isplitl [Hd Ha]
    · iexists d
      iframe Hd Ha Hn
      ipureintro; exact hf
    · ipureintro; exact hok
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    imod monoListAuthOwn_update_app [(WalOpG.save hs (cs.map walEntW)).toRaw] $$ Ha with ⟨Ha, -⟩
    iapply Hcommit
    iexists { d with H := d.H ++ [(WalOpG.save hs (cs.map walEntW)).toRaw] }
    iframe Hd Ha Hn
    ipureintro
    refine ⟨?_, hf.2.1, hf.2.2.1, ?_⟩
    · show walFoldChkFrom walFresh (walSrvHist (d.H ++ _)) = _
      rw [walSrvHist_snoc_save _ _ _ (fun c hcm => ⟨(hc c hcm).1, (hc c hcm).2.1⟩)]
      exact walFoldChkFrom_snoc_save hf.1 hok
    · intro hsz hs' es' hmem e he
      have hmem' : WalOpG.save hs' es' ∈ d.H.map WalOpG.toM ∨
          WalOpG.save hs' es' = WalOpG.save hs (cs.map walEntW) := by
        rw [List.map_append, List.mem_append, List.map_singleton, WalOpG.toM_toRaw,
          List.mem_singleton] at hmem
        exact hmem
      rcases hmem' with hmem' | heq
      · exact hf.2.2.2 hsz hs' es' hmem' e he
      · injection heq with h1 h2
        subst h2
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp he
        exact ⟨c, rfl, (hc c hcm).2.2 hsz⟩

/-- **`SaveSnap`'s update of the records as layer 1's** (the snapshot record appended), committing with a
lower bound of the history ending in the record (`walSnapRec_intro` makes the witness once it is synced). -/
theorem walRecs_saveSnapAU (h : WalH GF) (sized : Bool) (m : SnapshotMetadataM) (al : Bool) (Q : IProp GF) :
    (AU <{ ∃∃ (σ : StorContents), walRecs h σ sized ∗
          ⌜uint.nat m.Index' = σ.b → m.Term' = σ.base.term'⌝ }>
        @ WalFs.walAuMask, ∅ <{ walRecs h (walSaveSnap σ m) sized, COMM Q }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d ∗ ⌜d.sized = true⌝ }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc { d with H := d.H ++ [WalOpG.snap m al] },
          COMM Q ∗ monoListLbOwn h.γh (d.H ++ [WalOpG.snap m al]) }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, ⟨Hr, %hok⟩, Hcl⟩
  unfold walRecs
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplitr
  · ipureintro; exact hf.2.2.1
  isplit
  · iintro ⟨Hd, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    isplitl [Hd Ha]
    · iexists d
      iframe Hd Ha Hn
      ipureintro; exact hf
    · ipureintro; exact hok
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    imod monoListAuthOwn_update_app [WalOpG.snap m al] $$ Ha with ⟨Ha, #Hlb⟩
    imod Hcommit $$ [Hd Ha] with HQ
    · iexists { d with H := d.H ++ [WalOpG.snap m al] }
      iframe Hd Ha Hn
      ipureintro
      refine ⟨?_, hf.2.1, hf.2.2.1, ?_⟩
      · show walFoldChkFrom walFresh (walSrvHist (d.H ++ _)) = _
        rw [walSrvHist_snoc_snap]
        exact walFoldChkFrom_snoc_snap hf.1
      · intro hsz hs' es' hmem e he
        have hmem' : WalOpG.save hs' es' ∈ d.H.map WalOpG.toM ∨
            WalOpG.save hs' es' = (WalOpG.snap m al : WalOpG WalEnt).toM := by
          rw [List.map_append, List.mem_append, List.map_singleton, List.mem_singleton] at hmem
          exact hmem
        rcases hmem' with hmem' | heq
        · exact hf.2.2.2 hsz hs' es' hmem' e he
        · cases heq
    imodintro
    iframe HQ Hlb

/-- **The witness of a synced snapshot record**: a lower bound of the history ending in the record, the
record synced. -/
theorem walSnapRec_intro (h : WalH GF) (H : List (WalOpG WalEnt)) (m : SnapshotMetadataM) (al : Bool) :
    monoListLbOwn h.γh (H ++ [WalOpG.snap m al]) ∗ WalFs.walSyncedLb (W := h.W) h.dir h.γ.inc (H.length + 1) ⊢
      walSnapRec h H.length m := by
  iintro ⟨#Hl, #Hs⟩
  unfold walSnapRec
  iexists H ++ [WalOpG.snap m al]
  iframe Hl Hs
  ipureintro; exact ⟨al, by simp⟩

/-- The witness's record is synced. -/
theorem walSnapRec_synced (h : WalH GF) (i : Nat) (m : SnapshotMetadataM) :
    walSnapRec h i m ⊢ WalFs.walSyncedLb (W := h.W) h.dir h.γ.inc (i + 1) := by
  unfold walSnapRec
  iintro ⟨%H0, -, #Hs, -⟩
  iexact Hs

/-- **`Release`'s read of the records as layer 1's update of the WAL's locks** (at the snapshot record the
witness names: the history's position `i` is `snap m`, synced). -/
theorem walRecs_releaseAU (h : WalH GF) (i : Nat) (m : SnapshotMetadataM) (Q : IProp GF) :
    walSnapRec h i m ∗
      (AU <{ ∃∃ (σ : StorContents) (s : Bool), walRecs h σ s }> @ WalFs.walAuMask, ∅
        <{ walRecs h σ s, COMM Q }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d ∗
          ⌜(∃ al, d.H[i]? = some (WalOpG.snap ⟨m.ConfState', m.Index', m.Term'⟩ al)) ∧ i < i + 1⌝ }>
        @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc
            { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) m.Index') }, COMM Q }> := by
  iintro ⟨#Hw, Hau⟩
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %s, Hr, Hcl⟩
  unfold walRecs
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  iunfold walSnapRec at Hw
  icases Hw with ⟨%H0, #Hl, -, %hi⟩
  ihave %hv := mono_list_auth_lb_valid h.γh 1 d.H H0 $$ Ha Hl
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplitr
  · ipureintro
    obtain ⟨al, hi⟩ := hi
    exact ⟨⟨al, prefix_getElem? hv.2 hi⟩, Nat.lt_succ_self i⟩
  isplit
  · iintro ⟨Hd, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    iapply Hcommit
    iexists { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) m.Index') }
    iframe Hd Ha Hn
    ipureintro; exact hf

/-- **`Close`'s read of the records** (layer 1's identity update, from the records held): committing with
what makes the WAL's files once the history is synced and the lock and call permission are back. -/
theorem walRecs_closeAU (h : WalH GF) (σ : StorContents) (sized : Bool) (id cid : w64)
    (hb : σ.b ≤ σ.commit) :
    letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W
    walRecs h σ sized ∗ walMetaIs h id cid ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d,
          COMM (WalFs.walSyncedLb (W := h.W) h.dir h.γ.inc d.H.length ∗ WalFs.walUnlockedTok (W := h.W) ∗
              Fs.osCallPerm (Fs.callKey h.R h.dir) (1 : Qp).half -∗ walFiles h.toWalA id cid σ sized) }> := by
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W
  iintro ⟨Hr, Hm⟩
  iunfold walMetaIs at Hm
  icases Hm with %hm
  unfold walRecs
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro Iris.Std.LawfulSet.empty_subset
  iintro Hclose
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplit
  · iintro Hd
    imod Hclose with -
    imodintro
    iframe Hd Ha
  · iintro Hd
    imod Hclose with -
    imodintro
    iintro ⟨#Hs, Hu, Hp⟩
    unfold walFiles
    iexists h.γ.inc, d
    iframe Hd Hs Hn Hu Hp
    ipureintro
    refine ⟨?_, hf.1, hf.2.1.trans hm, hf.2.2.1, hf.2.2.2⟩
    exact walRead_of_fold hf.1 hb

/-- **What a restart reads from closed files is consecutive from its base, and its snapshot record is
at its base** (2026-11-27, the restart axiom's review R2: the WAL interface's I1 and I4 of `walReadFacts`,
proved of `walRead`; I2 and I3 are not facts of the read, `walRead` checks neither). -/
theorem walFiles_readShape (a : WalA GF) (id cid : w64) (σ : StorContents) (sized : Bool) :
    walFiles (GF := GF) a id cid σ sized ⊢ walFiles a id cid σ sized ∗
      ⌜walEntsWf σ ∧ ((σ.snap = none ∧ σ.base = entryID.mk (W64 0) (W64 0)) ∨
        ∃ m, σ.snap = some (SnapshotM.mk [] m) ∧ σ.base = entryID.mk m.Term' m.Index')⌝ := by
  unfold walFiles
  iintro ⟨%d, H1, H2, H3, H4, H5, %hp⟩
  have hr := hp.1
  isplitl [H1 H2 H3 H4 H5]
  · iexists d
    iframe H1 H2 H3 H4 H5
    ipureintro; exact hp
  · ipureintro
    refine ⟨walReadCut_wf (k := 0) (by rw [walReadCut_zero]; exact hr), ?_⟩
    unfold walRead at hr
    exact walFoldChkFrom_snapInv
      (fun sn b => (sn = none ∧ b = entryID.mk (W64 0) (W64 0)) ∨
        ∃ m, sn = some (SnapshotM.mk [] m) ∧ b = entryID.mk m.Term' m.Index')
      (fun m => Or.inr ⟨m, rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hr

end defs

end EtcdGrove
end Perennial
