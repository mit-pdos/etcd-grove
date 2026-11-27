/-
**`bootstrap`'s first start in parts: the hand-off states between its calls and the rows each
callee gives** (claim #34, stage 3, 2026-11-23; `notes/bootstrap-proof-plan.md` §7.3). Lean-first.
A defs module: the vocabulary of `bootstrap`'s callees' specs (`Spec/.../etcdserver/bootstrap*.lean`,
`bootstrappedCluster__Finalize.lean`) and the lemma joining their posts into `bootOk`
(`bootOk_of_parts`).

**The file system** (`bootstrap.go:53-81` at the etcd pin `edc800c6f`). `bootstrap` runs
`TouchDirAll(DataDir)`, `TouchDirAll(MemberDir())`, `bootstrapSnapshot`, `wal.Exist(WALDir())`,
`bootstrapBackend`, and `bootstrapStorage`. The start is `wal.bootRes cfg` (sealed, the WAL's slot).
The states:

- after `TouchDirAll(DataDir)`: `wal.bootRes cfg` again (`bootFs.touchData.law`): the data directory is
  an existing root, so `TouchDirAll` stats it, syncs its parent and probes `DataDir/.touch`
  (`IsDirWriteable`: written and removed), and the directory is empty again;
- after `TouchDirAll(MemberDir())`: `bootFs.memberDir cfg` (`bootFs.touchMember.law`): the member
  directory `DataDir/member` new, empty and wholly the caller's (`bootFs.dirFresh`), and the WAL's part
  (`bootFs.walPart`);
- `bootstrapSnapshot` takes the member directory and gives the snapshotter, the snapshot names' claims,
  the backend file's free name (`backend.fileFree (config.backendPathOf DataDir)`), which
  `bootstrapBackend` takes, and (2026-11-23) the snapshot directory's right, the claim on its other
  names (`snap.snapDirOwn`, `bootOk`'s `Hsdo`);
- `wal.Exist(WALDir())` answers `false` on the WAL's part (`bootFs.walExist.law`), which
  `bootstrapStorage` takes.

**Three laws, hypotheses of `bootstrap.wp_proof` until the data area's split law is proved** (plan
§7.3; "a proof takes a linked lemma as a law", CLAUDE.md). Each is true of Go:

- `bootFs.touchData.law`: **proved** (2026-11-23), `bootFs.touchData_law_holds` (`BootFsLaws.lean`), from
  `TouchDirAll.specExisting` (an existing directory; proved, `TouchDirAll.wp_proofExisting`) and the slot's
  `dataAreaFresh`, which since then holds `Fs.osAboveInv` (the root's parent is synced above the roots) and
  the bound `d.length < 4096`;
- `bootFs.touchMember.law`: `TouchDirAll.spec` covers it (`member` is absent in the data directory),
  but `wal.bootRes` is sealed, and its `dataAreaFresh` quantifies the file extension's instances
  existentially, where the file claims `bootOk` gives (`backend.fileFree`, `backend.bPath`) are at the
  program's (`backend.onFs`): its body must say they are the program's. (Until 2026-11-23 the snapshot
  directory's right `snap.snapDirOwn` was missing from it too; it is now `bootstrapSnapshot`'s, carved
  from the snapshot directory that function makes.)
- `bootFs.walExist.law`: **proved** (2026-11-23), `bootFs.walExist_law_holds` (`BootFsLaws.lean`), from
  `wal.Exist.spec` (whose post since then answers `false` with no WAL when the file system does not fail
  on the directory, `FsNoErrAt`): `ReadDir`'s `open` of the absent directory fails with `ENOENT`
  (`NoIoErr`'s `PathErrno`, its `open` case, the user's approval of 2026-11-23), at the area's no-I/O-error
  and no-lock-error instances, which cover every inode and (`a.Sio.path a.dir`) the WAL directory by path.

**The rows.** `bootOk`'s rows by the callee that makes them:

- `bootstrapSnapshot`: `Hss`, `Hsfree`, `Hsdo`;
- `bootstrapBackend`: `bootBackendRows` (`Hci HisCI Hcons Hbh Hthr Happ Hown Hmeta HmetaSnap Hbe HhkAt
  Hlate Hpath Hbfile`), `Hnew` at the data `D` after `CreateMetaBucket` (`bootBackendData`: `Hm0`,
  `HD`, the rest buckets empty, `HmEmpty`), and one write-back token for `Finalize`;
- `bootstrapCluster`: `Hbc`, `Hid`, the remotes nil (`Hrms Hrmsi Hrms0`) and `clusterBuilt`;
- `bootstrapStorage`: `Hsto`, `Hbw`, `Hwal`;
- `Finalize`: `bootClusterDone` (`Hcl Hrc Hcid Hclg Hvcn Hmembers Hisc HclBe Hmem`) and
  `Hnew` at `bootGo.withMemBkts D`: `SetBackend`'s `MustCreateBackendBuckets` creates the three
  membership buckets (one session, one write-back), so `HDr`'s membership part holds of the data
  after it, not before;
- `bootstrapRaft`: `bootRaftBuilt` (`Hraft`'s configuration part, `Hc Hlok Hreg Hγsz Hrauth Hmlock
  Hlog0 Hend Hsnone Hmeta Hfresh Hpeers Hctx`);
- `bootstrap` itself: `Hb`, `Hbk`, `Hbv`, `Hprt`; `Hraft`'s `γ.vs`/`srvBootLogOk` and `Hmem`'s
  `memBoot γ.boot` from its pure preconditions.

The shared existentials: `ps := bootGo.ps U tok` (`Hraft`, `Hmembers`), `cid := bootGo.cid U tok`
(`Hwal`, `Hcid`), `d` (`bootstrapBackend`'s, passed to `Finalize`: `HclBe`), `D := bootGo.withMemBkts
D₀` (`Hnew`, `Hm0`, `HD`, `HDr`, `HmEmpty`), `rms := []`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootValues

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-! ### The data after `Finalize`'s `SetBackend` (pure) -/

namespace bootGo

/-- **The data with the membership's buckets created** (`MustCreateBackendBuckets`,
`schema/membership.go:171-178`: `UnsafeCreateBucket` of `Members`, `MembersRemoved`, `Cluster`; bbolt's
`CreateBucket` makes an absent bucket empty and leaves a present one, `ErrBucketExists`, which the
backend ignores). -/
def withMemBkts [GooseExts] (D : backend.Data) : backend.Data :=
  ((D.insert go!"members" (backend.bktOf D go!"members")).insert go!"members_removed"
    (backend.bktOf D go!"members_removed")).insert go!"cluster" (backend.bktOf D go!"cluster")

theorem withMemBkts_lookup [GooseExts] (D : backend.Data) (n : GoString) :
    (withMemBkts D).lookup n =
      if n = go!"cluster" ∨ n = go!"members_removed" ∨ n = go!"members" then
        some (backend.bktOf D n) else D.lookup n := by
  unfold withMemBkts
  simp only [GMap.lookup_insert_eq_iff]
  by_cases h1 : go!"cluster" = n
  · subst h1; simp
  by_cases h2 : go!"members_removed" = n
  · subst h2; simp
  by_cases h3 : go!"members" = n
  · subst h3; simp
  have h : ¬ (n = go!"cluster" ∨ n = go!"members_removed" ∨ n = go!"members") := by
    rintro (h | h | h) <;> simp_all
  simp only [h1, h2, h3, h, ite_false]

/-! ### `MemberIDs()` is `ps` (claim #34 stage 4, 2026-11-25; pure) -/

theorem foldl_insert_isSome [GooseExts] (l : List apply.MemberM) (acc : GMap w64 apply.MemberM) (k : w64) :
    ((l.foldl (fun mem m => mem.insert m.id m) acc) !! k).isSome ↔
      (acc !! k).isSome ∨ k ∈ l.map (·.id) := by
  induction l generalizing acc with
  | nil => simp
  | cons m l ih =>
    rw [List.foldl_cons, ih]
    by_cases h : m.id = k
    · subst h; simp
    · have h' : k ≠ m.id := fun e => h e.symm
      simp [h, h']

/-- The members map's keys are the peers. -/
theorem memMap_isSome [GooseExts] (U : BootURLs) (t : GoString) (k : w64) :
    ((memMap U t) !! k).isSome ↔ k ∈ ps U t := by
  unfold memMap ps
  rw [foldl_insert_isSome]
  simp

/-- The peers are sorted (`mergeSort` by the ids' values). -/
theorem ps_sorted [GooseExts] (U : BootURLs) (t : GoString) :
    (ps U t).Pairwise (fun a b => a.toNat ≤ b.toNat) := by
  unfold ps members
  rw [List.pairwise_map]
  have h := List.pairwise_mergeSort (le := fun a b : apply.MemberM => decide (a.id.toNat ≤ b.id.toNat))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by
      by_cases hab : a.id.toNat ≤ b.id.toNat
      · simp [hab]
      · have : b.id.toNat ≤ a.id.toNat := by omega
        simp [this])
    ((U.initMap.domList.map (memberOf U t)))
  exact h.imp (fun hab => by simpa using hab)

/-- With distinct peers, strictly increasing. -/
theorem ps_lt [GooseExts] (U : BootURLs) (t : GoString) (hnd : (ps U t).Nodup) :
    (ps U t).Pairwise (fun a b => uint.Z a < uint.Z b) := by
  refine (ps_sorted U t).imp₂ (fun a b hab hne => ?_) (show (ps U t).Pairwise (· ≠ ·) from hnd)
  have hne' : a.toNat ≠ b.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
  simp only [uint.Z]
  omega

/-- Two strictly increasing lists of the same elements are equal. -/
theorem eq_of_pairwise_lt {l1 l2 : List w64} (h1 : l1.Pairwise (fun a b => uint.Z a < uint.Z b))
    (h2 : l2.Pairwise (fun a b => uint.Z a < uint.Z b)) (h : ∀ k, k ∈ l1 ↔ k ∈ l2) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons b l2 => exact absurd ((h b).2 (by simp)) (by simp)
  | cons a l1 ih =>
    cases l2 with
    | nil => exact absurd ((h a).1 (by simp)) (by simp)
    | cons b l2 =>
      rw [List.pairwise_cons] at h1 h2
      have hab : a = b := by
        apply Classical.byContradiction
        intro hne
        have ha : a ∈ b :: l2 := (h a).1 (by simp)
        have hb : b ∈ a :: l1 := (h b).2 (by simp)
        rcases List.mem_cons.1 ha with e | ha'
        · exact hne e
        rcases List.mem_cons.1 hb with e | hb'
        · exact hne e.symm
        have x1 := h2.1 a ha'
        have x2 := h1.1 b hb'
        omega
      subst hab
      congr 1
      apply ih h1.2 h2.2
      intro k
      constructor
      · intro hk
        rcases List.mem_cons.1 ((h k).1 (List.mem_cons_of_mem _ hk)) with e | e
        · subst e; have := h1.1 k hk; omega
        · exact e
      · intro hk
        rcases List.mem_cons.1 ((h k).2 (List.mem_cons_of_mem _ hk)) with e | e
        · subst e; have := h2.1 k hk; omega
        · exact e

/-- **`MemberIDs()` of the new cluster is `ps`**: the strictly increasing list of the members map's keys. -/
theorem ids_eq_ps [GooseExts] (U : BootURLs) (t : GoString) (hnd : (ps U t).Nodup) (ids : List w64)
    (hs : ids.Pairwise (fun a b => uint.Z a < uint.Z b))
    (hk : ∀ k, k ∈ ids ↔ ((memMap U t) !! k).isSome) : ids = ps U t :=
  eq_of_pairwise_lt hs (ps_lt U t hnd) (fun k => (hk k).trans (memMap_isSome U t k))

/-! ### The members map's entries (claim #34 stage 4, 2026-11-25; pure) -/

theorem foldl_insert_notin [GooseExts] (l : List apply.MemberM) (acc : GMap w64 apply.MemberM) (k : w64)
    (hk : k ∉ l.map (·.id)) :
    (l.foldl (fun mem m => mem.insert m.id m) acc) !! k = acc !! k := by
  induction l generalizing acc with
  | nil => rfl
  | cons m l ih =>
    rw [List.foldl_cons, ih]
    · have h : m.id ≠ k := fun e => hk (by simp [e])
      simp [h]
    · intro h; exact hk (by simp [h])

theorem foldl_insert_mem [GooseExts] (l : List apply.MemberM) (acc : GMap w64 apply.MemberM)
    (hnd : (l.map (·.id)).Nodup) (m : apply.MemberM) (hm : m ∈ l) :
    (l.foldl (fun mem m => mem.insert m.id m) acc) !! m.id = some m := by
  induction l generalizing acc with
  | nil => simp at hm
  | cons a l ih =>
    rw [List.foldl_cons]
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hm with rfl | hm'
    · rw [foldl_insert_notin _ _ _ hnd.1]; simp
    · exact ih _ hnd.2 hm'

theorem foldl_insert_some [GooseExts] (l : List apply.MemberM) (acc : GMap w64 apply.MemberM) (k : w64)
    (mm : apply.MemberM) (h : (l.foldl (fun mem m => mem.insert m.id m) acc) !! k = some mm) :
    acc !! k = some mm ∨ (mm ∈ l ∧ mm.id = k) := by
  induction l generalizing acc with
  | nil => left; exact h
  | cons a l ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨h1, h2⟩
    · rw [GMap.lookup_insert_eq_iff] at h1
      by_cases e : a.id = k
      · rw [if_pos e] at h1; cases h1; right; exact ⟨by simp, e⟩
      · rw [if_neg e] at h1; left; exact h1
    · right; exact ⟨by simp [h1], h2⟩

/-- A member of the initial cluster is its entry's `memberOf`. -/
theorem mem_members [GooseExts] (U : BootURLs) (t : GoString) (m : apply.MemberM) :
    m ∈ members U t ↔ ∃ name, (U.initMap !! name).isSome ∧ m = memberOf U t name := by
  unfold members
  rw [List.mem_mergeSort, List.mem_map]
  constructor
  · rintro ⟨name, hn, rfl⟩; exact ⟨name, (GMap.mem_dom_list _ _).1 hn, rfl⟩
  · rintro ⟨name, hn, rfl⟩; exact ⟨name, (GMap.mem_dom_list _ _).2 hn, rfl⟩

theorem memMap_lookup [GooseExts] (U : BootURLs) (t : GoString) (hnd : (ps U t).Nodup)
    (m : apply.MemberM) (hm : m ∈ members U t) : memMap U t !! m.id = some m := by
  unfold memMap
  exact foldl_insert_mem _ _ hnd m hm

theorem memMap_some [GooseExts] (U : BootURLs) (t : GoString) (k : w64) (mm : apply.MemberM)
    (h : memMap U t !! k = some mm) : mm ∈ members U t ∧ mm.id = k := by
  unfold memMap at h
  rcases foldl_insert_some _ _ _ _ h with h1 | h1
  · simp at h1
  · exact h1

/-- The members' names are distinct (each is its entry's key). -/
theorem memMap_names [GooseExts] (U : BootURLs) (t : GoString) (k1 k2 : w64) (m1 m2 : apply.MemberM)
    (h1 : memMap U t !! k1 = some m1) (h2 : memMap U t !! k2 = some m2) (hn : m1.name = m2.name) :
    k1 = k2 := by
  obtain ⟨hm1, rfl⟩ := memMap_some U t k1 m1 h1
  obtain ⟨hm2, rfl⟩ := memMap_some U t k2 m2 h2
  obtain ⟨n1, -, rfl⟩ := (mem_members U t m1).1 hm1
  obtain ⟨n2, -, rfl⟩ := (mem_members U t m2).1 hm2
  have : n1 = n2 := by simpa [memberOf] using hn
  subst this; rfl

/-- This member's entry. -/
theorem memMap_self [GooseExts] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (h : membersOk cfg U) :
    memMap U cfg.InitialClusterToken' !! id cfg U =
      some (memberOf U cfg.InitialClusterToken' cfg.Name') := by
  unfold id
  exact memMap_lookup U _ h.2.1 _ ((mem_members U _ _).2 ⟨_, h.1, rfl⟩)

/-- A boot member has a peer URL. -/
theorem members_urls [GooseExts] (U : BootURLs) (t : GoString) (hU : urlsNe U) (m : apply.MemberM)
    (hm : m ∈ members U t) : m.peerURLs ≠ [] := by
  obtain ⟨n, hn, rfl⟩ := (mem_members U t m).1 hm
  simpa [memberOf] using hU n hn

/-- A boot member is a voter with no client URLs, named by its entry. -/
theorem members_shape [GooseExts] (U : BootURLs) (t : GoString) (m : apply.MemberM)
    (hm : m ∈ members U t) : m.isLearner = false ∧ m.clientURLs = [] := by
  obtain ⟨n, -, rfl⟩ := (mem_members U t m).1 hm
  exact ⟨rfl, rfl⟩

end bootGo

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ### The file system's hand-off states -/

/-- **The WAL's part of the start** (`wal.bootRes`'s WAL conjuncts): the configuration's dedicated WAL
directory the member's (`srvWalDirOf`), and that WAL area fresh (`walAreaFresh`: what `wal.Create`
takes), handed through to `bootstrapStorage`'s `bootstrapNewWAL`. -/
def bootFs.walPart (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(⌜cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir'⌝ ∗ walAreaFresh (srvWalDirOf cfg.DataDir'))

/-- **A fresh directory `d`, wholly the caller's**, at the program's file-extension instances
(`backend.onFs`, where `backend.fileFree` and `backend.bPath` are): `dataAreaFresh`'s shape (a clean
absolute path, the whole of its spine, of its root's call permission and of its names, none naming an
entry), for a directory `TouchDirAll` has just made (its post: the new directory's whole claim, empty); and
(2026-11-23) the dispenser of the call permission above the roots (`Fs.osAboveInv`, persistent), which a
`TouchDirAll` inside it takes (`TouchDirAll.spec`; `syncDir` above the roots), and `d` shorter than `PATH_MAX`
(4096 bytes; the bound `TouchDirAll.spec` takes of a path below it follows). -/
def bootFs.dirFresh (d : GoString) : IProp GF :=
  backend.onFs iprop(∃ (R : Fs.Roots) (j : Fs.Ino) (h : Fs.NamesH),
    ⌜cleanAbsPath d ∧ d.length < 4096 ∧ ∀ b, h.cur !! b = none⌝ ∗ Fs.osInv ∗ Fs.osSharedInv R ∗
    Fs.osAboveInv ∗
    Fs.osPathS R d (DFrac.own 1) j ∗ Fs.osCallPerm (Fs.callKey R d) 1 ∗
    Fs.osNames j (.except []) (DFrac.own 1) h)

/-- **The state after `TouchDirAll(cfg.MemberDir())`** (`bootstrap.go:68`; see the file header): the
WAL's part, the member directory `DataDir/member` fresh (`MemberDir()` is
`filepath.Join(DataDir, "member")`, `config.go:300`). (Until 2026-11-23 also the snapshot directory's
right `snap.snapDirOwn`, now `bootstrapSnapshot`'s.) -/
def bootFs.memberDir (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(bootFs.walPart cfg ∗ bootFs.dirFresh (path.joinModel [cfg.DataDir', go!"member"]))

/-- **`TouchDirAll(lg, cfg.DataDir)` on the start** (`bootstrap.go:64`; a law, see the file header):
an error, or the start again. True of Go: the data directory exists (a root), so `TouchDirAll`
(`client/pkg/fileutil/fileutil.go:49-85`) checks its mode (a warning only), syncs its parent and
probes it with `.touch` (`IsDirWriteable`: `WriteFile` then `Remove`), leaving it empty. -/
abbrev bootFs.touchData.law : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ zapLoggerOk lg ∗
      wal.bootRes cfg }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll)) (Val #lg))
      (Val #cfg.DataDir'))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∨ ⌜err = interface.nil⌝ ∗ wal.bootRes cfg }}

/-- **`TouchDirAll(lg, cfg.MemberDir())` on the start** (`bootstrap.go:68`; a law, see the file
header): an error, or the member state. True of Go: `member` is absent in the fresh data directory, so
`TouchDirAll` makes it (`MkdirAll`, the parent synced, `IsDirWriteable`), empty. -/
abbrev bootFs.touchMember.law : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ zapLoggerOk lg ∗
      wal.bootRes cfg }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll)) (Val #lg))
      (Val #(path.joinModel [cfg.DataDir', go!"member"])))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∨ ⌜err = interface.nil⌝ ∗ bootFs.memberDir cfg }}

/-- **`wal.Exist(cfg.WALDir())` of the fresh WAL area answers `false`** (`bootstrap.go:77`; a law, see
the file header). True of Go: the area holds no WAL directory (`walAbsent`), so `fileutil.ReadDir`
fails with `ENOENT` and `Exist` returns `false` (`server/storage/wal/util.go:36-42`). -/
abbrev bootFs.walExist.law : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ bootFs.walPart cfg }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Exist)) (Val #cfg.DedicatedWALDir'))
  {{ RET #false; bootFs.walPart cfg }}

/-! ### The cluster before `Finalize` -/

/-- **The cluster `c` as `bootstrapNewClusterNoWAL` leaves it** (`bootstrap.go:379-414`), owned field
by field (not yet shared: no lock invariant, written with `structFieldRef`, not with
`membership.rcLockInv`, so that the version slot stage 1 adds to the lock invariant cannot break it).
Go: `NewClusterFromURLsMap(lg, token, InitialPeerURLsMap, WithMaxLearners(MaxLearners))`
(`membership/cluster.go:79-94`) is `NewCluster`'s literal (`:105-119`: `lg` the logger, or `zap.NewNop()`
for `nil`; empty `members` and `removed` maps; `downgradeInfo` `&DowngradeInfo{Enabled: false}`;
`maxLearners`; every other field zero: `localID` `0`, `be` nil, the mutex unlocked, `version` nil,
`versionChanged` nil), then one member per entry under its id (`NewMember(name, urls, token, nil)`:
`bootGo.memberOf`, so the map is `bootGo.memMap`, each member owned with its peer URLs' slice and a
nil client URLs' slice), then `genID()` sets `cid` (`bootGo.cid`). `MemberByName` and
`isMemberBootstrapped` only read it. -/
def clusterBuilt (c : Loc) (U : BootURLs) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) :
    IProp GF :=
  iprop(∃ (ms : GMap w64 Loc) (lgc rp dp : Loc),
    membership.rcLgAddr c ↦ lgc ∗ zapLoggerOk lgc ∗
    membership.rcLocalIDAddr c ↦ (W64 0 : w64) ∗
    membership.rcCidAddr c ↦ bootGo.cid U cfg.InitialClusterToken' ∗
    membership.rcBeAddr c ↦ (GoInterface.nil : GoInterface) ∗
    membership.rcMutexAddr c ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"version" c ↦
      (null : Loc) ∗
    membership.memAt c 1 ms (bootGo.memMap U cfg.InitialClusterToken') ∗
    membership.rcRemovedAddr c ↦ rp ∗ rp ↦$ (∅ : GMap w64 Bool) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"downgradeInfo" c ↦
      dp ∗
    dp ↦ (go_etcd_io.etcd.server.v3.etcdserver.version.DowngradeInfo.mk [] false) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"maxLearners" c ↦
      cfg.MaxLearners' ∗
    membership.rcVersionChangedAddr c ↦ (null : Loc))

/-- **The cluster `c` after `Finalize`, as `bootOk` names it** (`bootstrap.go:512-527`): its rows
`Hcl Hrc Hcid Hclg Hvcn Hmembers Hisc HclBe Hmem`, at the cluster's id `bootGo.cid`, the peers
`bootGo.ps`, the directory `bootGo.dir` and the members `bootGo.memMap`, on the backend at `be`.
(Stage 1, `ea2dc2dcf2`: `Hclok` and `Hcvm` left `bootOk`, lemmas of `Hrc`; `Hisc` is the rest of the
cluster's apply contract, `clusterApplyRest`.) -/
def bootClusterDone (U : BootURLs) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c be : Loc) :
    IProp GF :=
  iprop("#Hcl" ∷ rnClusterOk c ∗ "#Hrc" ∷ membership.isRaftCluster c ∗
    "#Hcid" ∷ membership.clusterCid c (bootGo.cid U cfg.InitialClusterToken') ∗
    "#Hclg" ∷ (∃ lgc : Loc, membership.rcLgAddr c ↦□ lgc ∗ zapLoggerOk lgc) ∗
    "Hvcn" ∷ (∃ v : Loc, membership.rcVersionChangedAddr c ↦ v) ∗
    "#Hmembers" ∷ srvMembersDir c (bootGo.ps U cfg.InitialClusterToken')
      (bootGo.dir U cfg.InitialClusterToken') ∗
    "#Hisc" ∷ clusterApplyRest c ∗
    "HclBe" ∷ clusterBeOn c be ∗
    "Hmem" ∷ membership.clusterMem c (bootGo.memMap U cfg.InitialClusterToken'))

/-! ### The backend -/

/-- **The backend's facts `bootstrapBackend` leaves on its data `D`** (pure; a fresh file and
`CreateMetaBucket`'s empty `Meta`): the meta keys the apply protocol's initial ones (`Hm0`), the `Key`
bucket empty (`HD`), every rest bucket empty or absent (`HDr`'s first part), and `Meta` empty
(`HmEmpty`). `Finalize`'s buckets come after (`bootGo.withMemBkts`). -/
def bootBackendData (γA : ApplyNames) (d : mvcc.KBReal) (D : backend.Data) : Prop :=
  metaIs D γA.m0 ∧ mvcc.keyView (backend.vData d.P (D, ⟨∅, W64 0⟩)) ∅ ∧
    (∀ n ∈ mvcc.restBuckets, (D.lookup n).getD ∅ = ∅) ∧
    (D.lookup go_etcd_io.etcd.server.v3.storage.schema.metaName).getD ∅ = ∅

/-- **The backend constructor's post at the server's resources**, `bootOk`'s `Hnew` (`backend.New`'s
`newPostK` at the apply protocol `γA`'s batch lock, the store's late registration, and `bootLeft N`),
over the data `D`. -/
def bootBackendNew (N : Nat) (γA : ApplyNames) (d : mvcc.KBReal) (D : backend.Data) : IProp GF :=
  backend.newPostK d.γB d.P (fun _ => mvcc.api.mvccW d.gx)
    (fun γB => batchLockInv γA (metaTM γB d.P)) (bootLeft N) d.be D

/-- **The rows of `bootOk` that `bootstrapBackend` makes, but `Hnew`** (`bootstrap.go:259-309`):
`Hci HisCI Hcons Hbh Hthr Happ Hown Hmeta HmetaSnap Hbe HhkAt Hlate Hpath Hbfile`, verbatim. -/
def bootBackendRows (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (bk : bootstrappedBackend)
    (γA : ApplyNames) (cil : Loc) (d : mvcc.KBReal) (CP : w64 → w64 → IProp GF)
    (Rw : TRow GF := TRow.triv) : IProp GF :=
  iprop("%Hci" ∷ ⌜bk.ci' = ciIface cil⌝ ∗
    "#HisCI" ∷ isCI cil γA.ci CP ∗ "#Hcons" ∷ inv applyN (consInv γA Rw) ∗
    "#Hbh" ∷ (∃ lgh : Loc, storage.isBackendHooks bk.beHooks'
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩
      lgh) ∗
    "Hthr" ∷ applyThread γA ⟨γA.m0.1, γA.m0.1, W64 0, false⟩ ∗
    "Happ" ∷ ciApplying cil (W64 0) (W64 0) ∗ "Hown" ∷ ciOwner cil bk.be' ∗
    "#Hmeta" ∷ isMetaBackend bk.be' (⊤ \ ↑applyN) (readView γA) ∗
    "#HmetaSnap" ∷ □ (∀ (π : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (D : backend.Data),
        ⌜ciKeys P ∧ metaIs D π.m0 ∧ π.bwb = γB.wb ∧ π.bopn = γB.opn⌝ -∗
        backend.hkOwn γB (backend.hkData P D) -∗ backend.bFresh γB -∗
        backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ∗
        □ ∀ (W : IProp GF) (b : Loc),
          backend.isBackend γB P W (batchLockInv (γA.withPh π) (metaTM γB P)) b -∗
          isMetaBackend (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN)
            (readView (γA.withPh π))) ∗
    "%Hbe" ∷ ⌜bk.be' = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be ∧
      mvcc.bridgeParams d.P ∧ ciKeys d.P ∧ storage.hooksParams d.P ∧
      d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧
      mvcc.leaseParams d.P ∧
      d.P.has mvcc.alarmBI ∧ d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧
      d.P.has mvcc.authRolesBI ∧
      d.P.has mvcc.membersBI ∧ d.P.has mvcc.membersRemovedBI ∧ d.P.has mvcc.clusterBI⌝ ∗
    "#HhkAt" ∷ backend.hooksAt d.be (storage.hooksIface bk.beHooks') ∗
    "Hlate" ∷ mvcc.api.mvccWReg d.gx ∗
    "Hpath" ∷ backend.bPath d.γB.db (config.backendPathOf cfg.DataDir') ∗
    "#Hbfile" ∷ backend.bFile d.γB (config.backendPathOf cfg.DataDir'))

end defs

section raft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **The raft configuration `raftConfig(cfg, id, s)` builds** (`bootstrap.go:584-596`; claim #34 stage
4, 2026-11-25): `ID` the member's id, `ElectionTick` the configuration's, `HeartbeatTick` `1`, the
storage the `MemoryStorage` `s` (as raft's `Storage` interface), `MaxSizePerMsg` `maxSizePerMsg`
(`2 ^ 20`, `raft.go:38`), `MaxInflightMsgs` `maxInflightMsgs` (`512`, `raft.go:41`), `CheckQuorum`,
`PreVote` the configuration's, the logger `lok` (`NewRaftLoggerZap`'s), every other field zero. -/
def raftCfgOf (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64) (s : Loc)
    (lok : GoInterfaceOk) : Config :=
  { (zero_val Config) with
    ID' := id, ElectionTick' := cfg.ElectionTicks', HeartbeatTick' := W64 1,
    Storage' := memStorIface s, MaxSizePerMsg' := W64 1048576, MaxInflightMsgs' := W64 512,
    CheckQuorum' := true, PreVote' := cfg.PreVote', Logger' := interface.ok lok }

/-- **The raft record `bv` as `bootstrapRaftFromCluster` makes it** (`bootstrap.go:548-572`,
`raftConfig` `:584-596`): `bootOk`'s `Hraft` but its facts of the peers and of `γ`, and `Hc Hlok Hreg
Hγsz Hrauth Hmlock Hlog0 Hend Hsnone Hmeta Hfresh Hpeers Hctx`, at this member's id `bootGo.id`, the
peers `bootGo.ps` (`MemberIDs()`) and their contexts `bootGo.ctxs` (`json.Marshal(cl.Member(id))`). -/
def bootRaftBuilt (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (bv : bootstrappedRaft) : IProp GF :=
  iprop(∃ (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames) (pv : List Peer),
    "%Hraft" ∷ ⌜rnStartCfg bv cv lok pv (bootGo.ps U cfg.InitialClusterToken') ∧
      bv.heartbeat' = cfg.TickMs' * W64 1000000 ∧ bv.lg' = cfg.Logger' ∧
      cv.ID' = bootGo.id cfg U⌝ ∗
    "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
    "#Hreg" ∷ memStorReg bv.storage' γs ∗ "%Hγsz" ∷ ⌜γs.sz = true⌝ ∗
    "Hrauth" ∷ memStorRegAuth (GMap.insert bv.storage' γs.tuple (∅ : GMap Loc MemStorNamesRec)) ∗
    "#Hmlock" ∷ memStorLock bv.storage' γs ∗
    "#Hlog0" ∷ memLog γs 0 DFrac.discard [(zero_val EntryM : EntryM)] ∗ "Hend" ∷ memEnd γs 1 ∗
    "Hsnone" ∷ memSnapNone γs memSnapEmpty ∗
    "Hsmeta" ∷ memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
    "Hfresh" ∷ memStorFresh bv.storage' γs 0 memSnapEmpty ∗
    "Hpeers" ∷ bv.peers' ↦* pv ∗ "#Hctx" ∷ peersCtx pv (bootGo.ctxs U cfg.InitialClusterToken'))


/-- **`bootBackendData` after `Finalize`'s buckets** (pure): the data with the membership's buckets
created keeps the meta keys, the empty `Key` bucket and the empty `Meta`, its rest buckets are empty,
and the three membership buckets are present and empty: `bootOk`'s `Hm0 HD HDr HmEmpty`. -/
theorem bootBackendData_withMemBkts (γA : ApplyNames) (d : mvcc.KBReal) (D : backend.Data)
    (h : bootBackendData γA d D) :
    metaIs (bootGo.withMemBkts D) γA.m0 ∧
    mvcc.keyView (backend.vData d.P (bootGo.withMemBkts D, ⟨∅, W64 0⟩)) ∅ ∧
    ((∀ n ∈ mvcc.restBuckets, ((bootGo.withMemBkts D).lookup n).getD ∅ = ∅) ∧
      (bootGo.withMemBkts D).lookup go!"members" = some ∅ ∧
      (bootGo.withMemBkts D).lookup go!"members_removed" = some ∅ ∧
      (bootGo.withMemBkts D).lookup go!"cluster" = some ∅) ∧
    ((bootGo.withMemBkts D).lookup go_etcd_io.etcd.server.v3.storage.schema.metaName).getD ∅ = ∅ := by
  obtain ⟨hm, hk, hr, he⟩ := h
  have hb : ∀ n, (n = go!"cluster" ∨ n = go!"members_removed" ∨ n = go!"members") →
      backend.bktOf D n = ∅ := by
    intro n hn
    exact hr n (by rcases hn with rfl | rfl | rfl <;> simp [mvcc.restBuckets])
  have hl : ∀ n, (bootGo.withMemBkts D).lookup n =
      if n = go!"cluster" ∨ n = go!"members_removed" ∨ n = go!"members" then some ∅
      else D.lookup n := by
    intro n
    rw [bootGo.withMemBkts_lookup]
    split
    · next hn => rw [hb n hn]
    · rfl
  have hdget : backend.dget (bootGo.withMemBkts D) = backend.dget D := by
    funext n k
    unfold backend.dget
    rw [hl n]
    split
    · next hn =>
      have := hb n hn
      unfold backend.bktOf at this
      cases hD : D.lookup n with
      | none => rfl
      | some m => rw [hD] at this; simp only [Option.getD_some] at this; subst this; rfl
    · rfl
  have hv : backend.vData d.P (bootGo.withMemBkts D, ⟨∅, W64 0⟩) =
      backend.vData d.P (D, ⟨∅, W64 0⟩) := by
    apply GMap.ext
    intro nk
    simp only [backend.vData, backend.vOf, hdget]
  refine ⟨?_, hv ▸ hk, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · unfold metaIs; rw [hdget]; exact hm
  · intro n hn
    rw [hl n]
    split
    · rfl
    · exact hr n hn
  · rw [hl]; simp
  · rw [hl]; simp
  · rw [hl]; simp
  · rw [hl]
    split
    · next hn => exact absurd hn (by decide)
    · exact he

/-- **The callees' posts join into `bootOk`** (see the file header): the records `bootstrap` holds
(its own literal `b`, `bootstrapStorage`'s `sto` and `bw`, `bootstrapBackend`'s `bk`,
`bootstrapCluster`'s `bc`, `bootstrapRaft`'s `bv`), the round tripper a `*http.Transport`, the WAL
(`bootstrapStorage`), the snapshot rows (`bootstrapSnapshot`'s, `snapDirOwn` among them),
`bootRaftBuilt`, `bootClusterDone`, `bootBackendRows` and `Hnew` after `Finalize`'s buckets give
`bootOk` at Go's values, given `bootstrap.spec`'s pure preconditions on `γ` and the facts the callees'
posts state (`membersOk`, this node's id, no remotes, `bootBackendData`). Framing, but for the
existentials (`ps`, `cid`, `rms := []`, `D := withMemBkts D₀`) and the data's facts
(`bootBackendData_withMemBkts`). -/
theorem bootOk_of_parts (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (N : Nat) (b : Loc) (bs : bootstrappedServer) (sto : bootstrappedStorage)
    (bk : bootstrappedBackend) (bw : bootstrappedWAL) (bc : bootstrappedCluster)
    (bv : bootstrappedRaft) (γA : ApplyNames) (cil : Loc) (d : mvcc.KBReal) (D : backend.Data)
    (hvs : γ.vs = bootGo.ps U cfg.InitialClusterToken')
    (hlog : srvBootLogOk (bootGo.ps U cfg.InitialClusterToken') γ.boot)
    (hmem : memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken')
    (hok : bootGo.membersOk cfg U) (hid : bc.nodeID' = bootGo.id cfg U)
    (hrm : bc.remotes' = slice.nil) (hD : bootBackendData γA d D) :
    (b ↦ bs : IProp GF) ∗ bs.storage' ↦ sto ∗ sto.backend' ↦ bk ∗ sto.wal' ↦ bw ∗ bs.cluster' ↦ bc ∗
      bs.raft' ↦ bv ∗
      ⌜∃ t : Loc, bs.prt' =
        GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.net.http.Transport.ty, #t⟩⌝ ∗
      wal.bootOk cfg (bootGo.id cfg U) (bootGo.cid U cfg.InitialClusterToken') bw.w' ∗
      snap.isSnapshotter bs.ss' (config.snapDirOf cfg.DataDir') ∗
      snap.snapDirOwn (snap.snapDBPath (config.snapDirOf cfg.DataDir')) ∗
      snapFreeAll (snap.snapDBPath (config.snapDirOf cfg.DataDir')) ∗
      bootRaftBuilt cfg U bv ∗ bootClusterDone U cfg bc.cl' d.be ∗
      bootBackendRows cfg bk γA cil d (srvCIPair γ.cl) ∗ bootBackendNew N γA d (bootGo.withMemBkts D) ⊢
    bootOk cfg γ (bootGo.id cfg U) (bootGo.ctxs U cfg.InitialClusterToken') N
      (bootGo.dir U cfg.InitialClusterToken') b := by
  obtain ⟨hm0, hkv, hdr, hme⟩ := bootBackendData_withMemBkts γA d D hD
  obtain ⟨-, hnd, hnz, hin⟩ := hok
  iintro ⟨Hb, Hsto, Hbk, Hbw, Hbc, Hbv, %Hprt, Hwal, #Hss, Hsdo, Hsfree, Hr, Hcl, Hbe, Hnew⟩
  iunfold bootRaftBuilt at Hr
  iNamed Hr
  iunfold bootClusterDone at Hcl
  iNamed Hcl
  iunfold bootBackendRows at Hbe
  iNamed Hbe
  ihave #Hrms : bc.remotes' ↦*□ ([] : List Loc) $$ []
  · rw [hrm]; iapply ownSlice_nil
  iunfold bootOk
  iexists bs, sto, bk, bw, bc, bv, cv, lok, γs, pv, bootGo.ps U cfg.InitialClusterToken', [],
    bootGo.cid U cfg.InitialClusterToken', cil, γA, d, bootGo.withMemBkts D
  iunfold bootBackendNew at Hnew
  rw [hmem]
  iunfold srvMembersDir at Hmembers
  iframe Hb Hsto Hbk Hbw Hbc Hbv Hwal Hss Hsdo Hsfree Hc Hlok Hreg Hrauth Hmlock Hlog0 Hend Hsnone
    Hfresh Hpeers Hctx Hcl Hrc Hcid Hclg Hvcn Hrms Hmembers Hisc HclBe Hmem HisCI
    Hcons Hbh Hthr Happ Hown Hmeta HmetaSnap HhkAt Hnew Hlate Hpath Hbfile Hsmeta
  obtain ⟨hcfg, hhb, hlg, hcid⟩ := Hraft
  isplitr
  · ipureintro; exact Hprt
  isplitr
  · ipureintro
    exact ⟨hcfg, hhb, hlg, hcid, hnd, hnz, by rw [hcid]; exact hin, hvs, hlog⟩
  isplitr
  · ipureintro; exact Hγsz
  isplitr
  · ipureintro; exact hid
  isplitr
  · iapply BigSepL.bigSepL_nil.2; itrivial
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact Hci
  isplitr
  · ipureintro; exact Hbe
  isplitr
  · ipureintro; exact hm0
  isplitr
  · ipureintro; exact hkv
  isplitr
  · ipureintro; exact hdr
  ipureintro; exact hme

end raft

end EtcdGrove
end Perennial
