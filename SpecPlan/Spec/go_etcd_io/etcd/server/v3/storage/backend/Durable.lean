/-
# The backend's file and crashes, over bbolt's (batch 4a, round 1)

The laws that tie 4a's file vocabulary to 4c's (`SpecPlan/Spec/go_etcd_io/bbolt/Api.lean`): only the opener
(2e's `OpenBackend`, `OpenSnapshotBackend`, the restart) and the crash argument import this module.

* `imgOf D`: bbolt's data as etcd sees it (the root's buckets and their plain values; sequence
  counters dropped; nested buckets, which etcd never makes, read as absent values).
* `beFile_bytes`: a file of an image's bytes (`imgBytes`) is a backend file of it (verify-round).
* `beFile_of`: **a file bbolt holds is a backend file of its image** (4c's `fileHolds`, from
  `fileHolds_new` for a fresh path or a deleted file, `fileHolds_image` for a received snapshot's
  file, or the crash law): so `New` can be called. `beFile_none`: an absent path (`osMeta … none`)
  or an empty file with nothing past its end, named or not (second pass: `New` starts it through
  4c's `boltFresh_alloc`, the state `BoltSt.fresh`, whose name is not durable).
* **Unsynced renames** (second pass, server-boot's request): `OpenSnapshotBackend` renames a
  snapshot file onto the backend's path with no directory fsync (`backend.go:61-70`; the next
  `SaveDBFrom`'s fsync of the same directory makes it durable). A crash before that may bring the
  destination's previous file back. `beRevs p os` (exclusive; a list since the re-review, A8 N3:
  two installs before a directory sync are reachable, `raft.go:284,307`, and a journaling file
  system may keep a prefix of the unsynced renames, so any previous file may come back): the files
  `os` a crash may bring back at `p` (closed, so fixed), `[]` none (`beNoRevert p`).
  The file laws (`beFile_of`, `beFile_bytes`, `beFile_none`) give `beNoRevert` (4c's `fileHolds` is
  of a durably named file); the rename's bridge (server-boot's trusted `Snap.dbFile_rename`, until
  OsFs has `rename`) consumes the destination's `beFile p o0 ∗ beRevs p os` and gives the renamed
  file's `beFile p (some I) ∗ beRevs p (o0 :: os)`; the directory fsync (server-boot's `SaveDBFrom`)
  turns `beRevs p os` into `beNoRevert p`. Realization: OsFs's name state of `p` (`named`) with the
  previous inode's contents; **needs OsFs's crash relation for an unsynced rename to bring the old
  entry back** (4c's `boltCrash` says only "may be gone" for `named = false`): recorded as a gap.
  **The rename's source** (third crash pass, F2-crash N1): a rename that brings `p`'s previous file
  back also brings its source back (one directory's two entries, kept or lost together), which this
  module cannot say (the source is the snapshotter's). The snapshotter's crash laws
  (`Snap.snapDbs_crash`, `snapSaving_crash`) take the newest install's rename record with
  `beRevs p os` and give it back resolved (`[]` if the rename is kept; unchanged, with the source
  back, if lost), at the crashed generation; the frame applies them before `beFile_crash`/`beCrash`,
  whose statements are unchanged.
* `beCrash`: **a crash leaves the file at one of the committed images** (4c's `boltCrash`, over the
  history the client keeps in an invariant): from the file's crash invariant `beDurInv γ p`, crash
  safety on (`beSynced γ`: `UnsafeNoFsync` off), the client's `beHist γ L` (any fraction of bbolt's
  state is folded into it: the realization keeps one in the history's authority) and OsFs's restart
  resources, the next generation gets `beFile p (some I)` for some `I ∈ L`; or, for a file created
  in this generation whose name was not yet durable (4c's `boltCrash`, `named = false`), no file
  (`beFile p none`, with `Image.empty ∈ L`: such a file began empty); or, with a pending rename
  (`beRevs p os`), any of the previous files `os`. The revert state comes back `beNoRevert`. Serves 2d's item 3 (a
  restart finds a committed image, whose meaning the server's invariant attached at its commit),
  2e's `memberDisk`, 3c's item 4 (a session's writes land in one commit).

* **Which law applies, at every point** (repair3-boot, the crash pass's requests 1 and 2): the
  client's crash state holds the file closed (`beFile p o`) until `New`'s `beOpenUpd` fires at
  bbolt's open, then open (`beDurInv ∗ beSynced ∗ beHist`) until `Close`'s `beCloseUpd` fires at the
  release after `DB.Close`, then closed again (`Api.lean`'s header). Realization of the swaps: 4c's
  `fileHolds_alloc` (at the open) and `boltRelease` (at the close, with the history authority's
  share of `boltState`, freed by the client's `beHist`), both in `beFileN`; 4c's `Open` and
  `DB.Close` keep the file in `boltFile`'s crash invariant between them. `beCrash` before the
  swaps was not true after `Close` returned (the post gave the file away while the client kept the
  history: two laws for one file, `beCrash`'s without the file's resources).
* `beFile_crash` (verify round, crash pass: R-A8 N4): **a closed file at rest crosses a crash**
  unchanged (a bbolt file's last commit was fsynced before `Close`), or reverted to a previous file
  of a pending rename, or gone if its name is not durable (second crash pass, G-a: the open's update
  put `none` in the revert list); 2e's `disk_crash` uses it for a member whose backend is closed
  (before `OpenBackend`, after `Close`), `beCrash` for an open one.
* **A file renamed over while open** (second crash pass, G-b: `applySnapshot` renames the snapshot's
  file onto the backend's path before it closes the old backend, `server.go:1068,1144`): the rename's
  update over the open form (`beAt p (.opened γ L)`) keeps the old backend's history with the client
  and gives `beDetached γ p`; the old backend's `Close` (`beCloseUpd`'s detached form) puts its final
  image into the revert list; a crash before that close folds it in first (`beDetached_crash`, at
  the crashed generation: some committed image of the old history, which a crash before a directory
  sync may bring back at `p`), and then the new file's law (`beFile_crash` or `beCrash`) applies.
  Realization: the old inode's resources stay in 4c's `boltFile` of `γ` until its release; the revert
  entry needs OsFs's `rename` (the recorded gap, `notes/perennial-changes.md`).

The next generation's `beFile` is at the next generation's heap (`⟨hG.goose_globalGS, L'⟩`), as
`Bbolt.boltCrash`'s `fileHolds` (verify-round, A10-provability B2: it was stated at the crashed
generation's heap, which `boltCrash` does not give and a restart cannot use). This needs the heap
binders on the opaque predicates, which landed at `1aa6fc1337` (`#check @beFile` takes `hG`); the
gap recorded at integration I6 (item 2) is closed. `HasExt osFsExt` stays a binder of the three
laws here only: a realization over 4c's predicates holds it as `∃ _ : HasExt osFsExt, …` (a `Prop`
class, proof-irrelevant), and every triple's predicates come from `New`, whose premise `beFile`
carries it.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import SpecPlan.Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section model
variable [GooseExts]

open Classical in
/-- **bbolt's data as etcd sees it**: the root's buckets and their plain values. -/
def imgOf (D : Bbolt.Data) : Image :=
  { made := fun b => decide (Bbolt.Ent.bktAt D [b]),
    ents := fun b k => match D.atPath [b, k] with
      | some (.val v) => some v
      | _ => none,
    clean := fun _ => true }

end model

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A file bbolt holds is a backend file of its image** (durably named: no rename pending). -/
def beFile_of.spec : Prop :=
  ∀ [HasExt osFsExt] (p : GoString) (D : Bbolt.Data),
    Bbolt.fileHolds (GF := GF) p D ⊢ beFile p (some (imgOf D)) ∗ beNoRevert p

/-- **A file of an image's bytes is a backend file of the image** (verify-round, A10-completeness
F1: a snapshot's bytes written to a file and opened, `ReqSnapshotFresh`; 2e's received snapshot
file). Realization: `imgBytes I bs := ∃ D, Bbolt.boltImage bs D ∧ imgOf D = I`, then 4c's
`fileHolds_image` and `beFile_of`. -/
def beFile_bytes.spec : Prop :=
  ∀ [HasExt osFsExt] (p : GoString) (m : OsMeta) (xs : List (w8 × Bool)) (I : Image),
    ⌜imgBytes I (xs.map Prod.fst) ∧ (∀ x ∈ xs, x.2 = true) ∧ m.size = xs.length ∧
      m.lo = xs.length ∧ m.hi = xs.length ∧ m.named = true ∧ m.maps = ∅⌝ ∗
    osMeta (GF := GF) p (DFrac.own 1) (some m) ∗ osBytes (GF := GF) p 0 (DFrac.own 1) xs
    ⊢ beFile p (some I) ∗ beNoRevert p

/-- **No file at `p`, or an empty one with nothing past its end** (named or not): a backend file
that `New` starts empty through 4c's `boltFresh_alloc` (second pass). -/
def beFile_none.spec : Prop :=
  ∀ [HasExt osFsExt] (p : GoString) (mo : Option OsMeta),
    osMeta (GF := GF) p (DFrac.own 1) mo ∗
      (match mo with
       | none => iprop(emp)
       | some m => iprop(⌜m.size = 0 ∧ m.hi = 0 ∧ m.maps = ∅⌝ ∗
           osBytes (GF := GF) p 0 (DFrac.own 1) []))
    ⊢ beFile p none ∗ beNoRevert p

/-- One revert state per path. -/
def beRevert_excl.spec : Prop := ∀ p os os',
  beRevertL (GF := GF) p os ∗ beRevertL p os' ⊢ iprop(False)

def beNoRevert_excl.spec : Prop := ∀ p,
  beNoRevert (GF := GF) p ∗ beNoRevert p ⊢ iprop(False)

def beRevert_noRevert.spec : Prop := ∀ p os,
  beRevertL (GF := GF) p os ∗ beNoRevert p ⊢ iprop(False)

/-- **The crash law** (see the header): the next generation `L'` finds the file at one of the
committed images; or no file, if the file was created empty in this generation and its name was not
yet durable; or, with renames onto `p` pending (`os`), any of the previous files. -/
def beCrash.spec : Prop :=
  ∀ [HasExt osFsExt] (L' : GooseLocalGS GF) (γ : BeNames) (p : GoString) (L : List Image)
    (os : List (Option Image)) (Ps : List GoString),
    p ∉ Ps →
    beDurInv (GF := GF) γ p ∗ beSynced γ ∗ beHist γ L ∗ beRevs p os ∗ crashed ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Ps ⊢
    |={⊤}=> ∃ o : Option Image,
      ⌜(∃ I, o = some I ∧ I ∈ L) ∨ (o = none ∧ Image.empty ∈ L) ∨ o ∈ os⌝ ∗
      @beFile _ _ _ GF ⟨hG.goose_globalGS, L'⟩ p o ∗
      @beNoRevert _ _ _ GF ⟨hG.goose_globalGS, L'⟩ p ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (p :: Ps)

/-- **A closed file crosses a crash** (verify round, crash pass: R-A8 N4; server-boot's): the
backend's file at rest (`beFile p o`: closed, so no commit in flight; a member before `OpenBackend`,
or after `Close`), with its revert state, gives the next generation `L'` the same file or, with
renames onto `p` pending or its name not durable (`os`), one of the previous files or none; the
revert state comes back `beNoRevert`. Taken out of the OS's crash rest `crashRest`. Realization:
`beFile p (some I)` is the file's OsFs resources at an image of `D` (`imgOf D = I`), every byte clean
and durable to the file's size, so OsFs's crash relation keeps its bytes (`crashRest_take` with
`osMeta`'s fragment); with its name durable, `fileHolds` at `L'`; with it not durable (`named =
false`), OsFs's D4 may drop the name, and then the revert state's `none` (the open's update put it
there: `beOpenUpd`) is the outcome (`beFile_none` at `L'`); `beFile p none` is `osMeta p none` or an
empty file, which a crash leaves absent or empty; the revert case is `beRevertL`'s (the unsynced
rename's old entry back), the same OsFs gap as `beCrash`'s (the header). Changes (second crash pass,
G-a): statement unchanged; it was false after a first boot's `Close` (the file `bolt.Open` created,
its directory never synced, may vanish), now true because that file's revert list holds `none`. True of the Go: a
bbolt file is written only while open (`Open` with `NoFreelistSync`, commits, `Close`), and each
commit fsyncs its pages and meta before `Close` returns (`UnsafeNoFsync` off: `beSynced`; a file
`OpenBackend` closed with `UnsafeNoFsync` on is not at rest in this sense, and 2e's `diskCfgOk`
excludes it). -/
def beFile_crash.spec : Prop :=
  ∀ [HasExt osFsExt] (L' : GooseLocalGS GF) (p : GoString) (o : Option Image)
    (os : List (Option Image)) (Ps : List GoString),
    p ∉ Ps →
    beFile (GF := GF) p o ∗ beRevs p os ∗ crashed ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Ps ⊢
    |={⊤}=> ∃ o' : Option Image, ⌜o' = o ∨ o' ∈ os⌝ ∗
      @beFile _ _ _ GF ⟨hG.goose_globalGS, L'⟩ p o' ∗
      @beNoRevert _ _ _ GF ⟨hG.goose_globalGS, L'⟩ p ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (p :: Ps)

/-- **A detached open file folds into the revert list at a crash** (second crash pass, G-b; see the
header): after the generation crashed, the old backend `γ` renamed over at `p` while open (its crash
invariant, crash safety, its history `L`) leaves at `p`, if the rename is lost (no directory sync
since), its file at some committed image `I ∈ L` (4c's `boltCrash` of `γ`'s file: the last fsynced
commit, or the one in flight), or no file if its name was never durable (then `none` is already in
`os`: the open's update). Stated at the crashed generation (no `L'`): it consumes the history and the
detached token, so the new file's crash law (`beFile_crash` or `beCrash`) then applies with the
extended list. Realization: `beRevertL`'s record gets `γ`'s entry from 4c's `boltCrash` of `γ`'s
file, at the old inode, which needs OsFs's `rename` (the recorded gap, as every revert entry). -/
def beDetached_crash.spec : Prop :=
  ∀ [HasExt osFsExt] (γ : BeNames) (p : GoString) (L : List Image) (os : List (Option Image)),
    beDetached (GF := GF) γ p ∗ beDurInv γ p ∗ beSynced γ ∗ beHist γ L ∗ beRevs p os ∗ crashed ⊢
    |={⊤}=> ∃ I : Image, ⌜I ∈ L⌝ ∗ beRevs p (some I :: os)

/-- **The package's bbolt options** (second pass, 4c's A11 F7: no keyed-literal spec in bbolt; the
initializer `&bolt.Options{MmapFlags: syscall.MAP_POPULATE, NoFreelistSync: true}`,
`config_linux.go:29-32`, is untranslated, `boltOpenOptions.init`): **assumed**, as this package's own
`PkgInit` fact. The global holds a pointer to options read-only for good, `MmapFlags` =
`MAP_POPULATE`, `NoFreelistSync` = `true` (tracked by 4c's `OptsM` since its re-review N1: with it,
`Open`'s internal freelist commit is skipped, so `Open` takes `emp` for that update; RR-raftlog-bbolt
NR2), every tracked field else at `bolt.Options{}`'s. `newBackend` loads it (`*bopts =
*boltOpenOptions`, 4c's `optsLoad`/`optsStore`). True of the Go: the literal above, never written
after initialization. -/
def boltOpenOptions_init.spec [HasExt osFsExt] : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ⊢
    ∃ l : Loc, globalAddr go_etcd_io.etcd.server.v3.storage.backend.boltOpenOptions ↦□ l ∗
      Bbolt.optsAt l DFrac.discard { Bbolt.OptsM.dflt with mmapFlags := W64 Bbolt.mapPopulate, noFreelistSync := true }

end laws

end Backend
end EtcdGrove
end Perennial
