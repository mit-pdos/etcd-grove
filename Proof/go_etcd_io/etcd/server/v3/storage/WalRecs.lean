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
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **A WAL area and directory** (see the section header): what a closed WAL's files are named by. -/
structure WalA (GF : BundledGFunctors) where
  ext : ExtSemantics Fs.fsExt
  semOk : Fs.FsSemOk (S := ext)
  has : HasExt Fs.fsExt
  W : WalFs.WalGS GF
  Sio : Fs.IoSet
  sat : Fs.FsStepSat (Fs.NoIoErr Sio) (S := ext)
  cov : WalFs.walCov Sio
  R : Fs.Roots
  jr : Fs.Ino
  r : GoString
  dir : GoString

/-- **An open WAL** (see the section header). -/
structure WalH (GF : BundledGFunctors) extends WalA GF where
  inj : go.BasicIntoValInj
  w : Loc
  γ : WalFs.WalShN
  md : List w8
  γh : GName

/-- **A share `q` of the open WAL `h`** (persistent area facts, the shared handle's share): every share
lets the storages over `h.w` write it (`Save`, `SaveSnap`, `Sync`, `Release`), the whole closes it
(`Close`). Until L3 a ghost variable over the opaque `walGName w`. -/
def storage.walOpen (h : WalH GF) (q : Qp) : IProp GF :=
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj
  iprop(WalFs.walOpenWS h.Sio walSrvP walSrvMr h.w h.dir h.γ q ∗
    WalFs.walAreaOk walCodec walSrvMr h.R h.jr h.r)

/-- The shares of an open WAL are fractional. -/
instance storage.walOpen_fractional (h : WalH GF) :
    Fractional (fun q => storage.walOpen (GF := GF) h q) where
  fractional q1 q2 := by
    letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj
    unfold storage.walOpen
    have hs := WalFs.walOpenWS_split (GF := GF) (hG := hG) h.Sio walSrvP walSrvMr h.w h.dir h.γ q1 q2
    constructor
    · iintro ⟨H, #Ha⟩
      icases hs.1 $$ H with ⟨H1, H2⟩
      iframe H1 H2 Ha
    · iintro ⟨⟨H1, #Ha⟩, ⟨H2, -⟩⟩
      ihave H := hs.2 $$ [H1 H2]
      · iframe H1 H2
      iframe H Ha

instance storage.walOpen_as_fractional (h : WalH GF) (q : Qp) :
    AsFractional (storage.walOpen (GF := GF) h q) ioΦ (fun q => storage.walOpen h q) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := storage.walOpen_fractional h

/-- **The WAL `h`'s records are `σ`** (sealed; exclusive, timeless): the WAL's durable state `d`
(`WalFs.walDiskAt`), whose history folds, unwrapped, to `σ` (`walFoldChkFrom walFresh`, the eager model
`walSave`/`walSaveSnap` step by step), its metadata `h.md`, its name durable (`walNamed`), with the
authority over the history's prefixes (`walSnapRec`, `walBaseLb`). Once `σ.b ≤ σ.commit`, what a restart
reads (`walRead_of_fold`). **`sized`**: every entry record is the wrap of a content `c` with
`entSizeOk c` (`walEntsSized`); `false` claims nothing more. -/
@[no_expose] def walRecs (h : WalH GF) (σ : StorContents) (sized : Bool := false) : IProp GF :=
  letI := h.W
  iprop(∃ d : WalDur, WalFs.walDiskAt h.dir d ∗ monoListAuthOwn h.γh 1 d.H ∗ WalFs.walNamed h.dir ∗
    ⌜walFoldChkFrom walFresh (walSrvHist d.H) = some σ ∧ d.metadata = h.md ∧
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
  iprop(∃ H0 : List (WalOpG WalEnt), monoListLbOwn h.γh H0 ∗ WalFs.walSyncedLb h.dir (i + 1) ∗
    ⌜H0[i]? = some (WalOpG.snap m)⌝)

/-- **The files of the closed WAL in the area and directory `a` hold the records `σ`, its metadata the
member `id` of the cluster `cid`** (exclusive, timeless): the durable state `d` all synced, its name
durable, the generation's lock free (`walUnlockedTok`) and the call permission's half of the directory's
root back (what `WAL.Close` returns), what a restart reads from it `σ` (`walRead`), its metadata
`walMetaEnc id cid`; `sized` as `walRecs`'. Until L3 an axiom (with `walFiles_timeless`). -/
@[no_expose] def walFiles (a : WalA GF) (id cid : w64) (σ : StorContents) (sized : Bool := false) :
    IProp GF :=
  letI := a.ext; letI := a.semOk; letI := a.has; letI := a.W
  iprop(∃ d : WalDur, WalFs.walDiskAt a.dir d ∗ WalFs.walSyncedLb a.dir d.H.length ∗ WalFs.walNamed a.dir ∗
    WalFs.walUnlockedTok ∗ Fs.osCallPerm (Fs.callKey a.R a.dir) (1 : Qp).half ∗
    ⌜walRead (walSrvHist d.H) = some σ ∧ d.metadata = walMetaEnc id cid ∧
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
  ipureintro; exact ⟨hf.1, hf.2.1, fun h => by cases h⟩

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

end defs

end EtcdGrove
end Perennial
