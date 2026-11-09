/-
# The snapshotter (`etcdserver/api/snap`): vocabulary (batch 2e)

The snapshotter keeps the **database snapshots** a member received (`<snap dir>/<index:016x>.snap.db`:
a leader's backend, sent in a merged `MsgSnap`), until the apply thread installs one as the member's
backend (`serverstorage.OpenSnapshotBackend`: a rename onto the backend's path) or a later snapshot
releases it (`ReleaseSnapDBs`). The package is translated names only (but `Message.GetTo`); its
specs are trusted, each stating what the Go code computes (`db.go`, `snapshotter.go`, `message.go`).

## Vocabulary

* `BeImage` (4a's `Backend.Image`), `beFile path o` (4a's `Backend.beFile`: verify-round, A8
  provability F5, the provisional name is now an abbreviation of 4a's, with 4a's laws
  `beFile_timeless`/`beFile_excl`): what a bbolt database file holds, as the backend reads it after
  an open (`none`: no file at `path`). A snapshot db file, the backend's own file and the image a
  leader streams are all `BeImage`s, so a rename carries the image unchanged.
* `dbPathOf sd i` (opaque pure function, as `Config`'s paths): `<sd>/<i:016x>.snap.db`
  (`Snapshotter.dbFilePath`), the path `DBFilePath` returns.
* `isSnapshotter ss sd` (persistent): `ss` is a `*Snapshotter` of directory `sd` (its fields
  read-only: the logger, the directory, the fsync function).
* `snapDbs sd F` (exclusive, timeless): **the database snapshots in `sd`**: `F i` is the image of
  `<sd>/<i:016x>.snap.db` (`none`: no such file). Intended realization: a ghost variable whose
  meaning ("what `os.Rename` of that file onto a path, then an open, reads") is trusted, as
  `Wal.walRecs`. Held by the server's invariant (the receiving transport adds, the apply thread
  installs and releases), by `EtcdServer.memberDisk` while the member is stopped. **`F` is the
  directory as a reader sees it now**; an addition is durable when `SaveDBFrom` returns (it fsyncs
  the file and the directory), a removal is not (`ReleaseSnapDBs`' `os.Remove` and
  `OpenSnapshotBackend`'s rename fsync no directory): see `snapGone`.
* `snapSaving sd F i img` (exclusive, timeless): **a `SaveDBFrom` of `img` at `i` is between its
  rename and its directory fsync, over the directory `F`** (verify-round, A8 provability F9: a crash
  then may or may not keep the new file). `SaveDBFrom`'s first update moves `snapDbs sd F` to it,
  its second to `snapDbs sd (saveAt F i img)`.
* `snapGone sd H` (exclusive, timeless): **the images removed from `sd`'s db files that a crash may
  bring back** (`H i img`: `img` was at `i` and was removed; the removals' directory entries are not
  fsynced). Client-owned with `snapDbs`, moved by the removals' updates (`ReleaseSnapDBs`, the
  install's rename `dbFile_rename`), as 4a's `beHist` is by commits; monotone (a later directory
  fsync makes the removals durable, which the model does not track: weaker, still true).
* `dbReader r img` (exclusive): **provisional, batch 2f's**: the `io.Reader` `r` yields the bytes
  of `img` and then `EOF` (or fails: a cut stream). rafthttp's merged-snapshot reader is one.
* `isMessage p to sz` (persistent) and `msgClose p` (exclusive, once): a `*snap.Message` to member
  `to`, of total size `sz`, whose reader closes once (`CloseWithError`).
* `rcClose rc` (exclusive, once): **provisional, Perennial's `io`**: `rc.Close()` may be called
  once (the reader `NewMessage` wraps; the axiom sweep's B3-3: a nil reader panics at the close).

## Laws

`isSnapshotter_persistent`, `snapDbs_timeless`, `snapDbs_excl`, `snapSaving_timeless`,
`snapSaving_excl`, `snapGone_timeless`, `snapGone_excl`, `isMessage_persistent`,
`msgCloseCh_persistent`; the trusted rename of a db file (`dbFile_rename`: `os.Rename` of
`dbPathOf sd i`, which `OpenSnapshotBackend` calls: verify-round, A8 provability F5, the bridge from
`os.Rename` to this model); the crash laws `snapDbs_crash`, `snapSaving_crash` (verify-round, A8
provability F9).

## Crashes

`snapCrashed F H F'` (transparent): what a crash leaves of the directory `F` with removed images
`H`: every present file stays (each was fsynced with its directory by `SaveDBFrom`), and an absent
one is absent or back with an image it had (`H`). During a save (`snapSaving sd F i img`) the file at
`i` may also be the new image. **Why it is true** (trusted, the files' meaning): `SaveDBFrom` writes
and fsyncs a temporary file, renames it, fsyncs the directory (and fsyncs the directory again when
the file is found there already, a rename a crash may not have kept: `db.go:58-64`); `os.Remove`
and `os.Rename` are atomic on the directory entry, not durable until a directory fsync. The laws
take the old generation's crash token (`crashed`) and give the next generation's `snapDbs` (at
`⟨hG.goose_globalGS, L'⟩`, as `Wal.walRecs_crash`). The backend file at the install's
destination, which an unsynced rename may also revert, is 4a's: `dbFile_rename`'s update adds the
destination's previous file to its revert state (`revertSt dst os`: every file a crash may bring
back, 4a's `beCrash`), and the next `SaveDBFrom`'s directory fsync, of the directory holding `dst`
(`inDir`), empties it (last pass, backend-schema's request; re-review N3 and the crash pass: the
list form, 4a's `beRevs`).

## Requirement snippets

`examples/specreq/etcdserverboot/snap.go` (`ReqSnapRoundTrip`: a received snapshot saved, found by
index, installed, older ones released).
-/
module

public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.snap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Snap

open Iris Iris.BI

/-- What a bbolt database file holds, as the backend reads it: 4a's `Backend.Image` (integration X). -/
abbrev BeImage : Type := Backend.Image

/-- **`p` is an entry of the directory `sd`** (`<sd>/<n>`, `n` without a `/`): what an fsync of
`sd` makes durable (`SaveDBFrom`'s directory fsync, for the backend file `<sd>/db`). -/
def inDir (sd p : GoString) : Prop :=
  ∃ n : GoString, p = sd ++ go!"/" ++ n ∧ ∀ b ∈ n, b ≠ W8 47

/-- **The path of the db file of index `i`** in `sd` (`<sd>/<i:016x>.snap.db`). -/
opaque dbPathOf (sd : GoString) (i : Nat) : GoString

/-- `ReleaseSnapDBs` at index `i`: the files of lower indices removed. -/
def releaseBelow (F : Nat → Option BeImage) (i : Nat) : Nat → Option BeImage :=
  fun j => if j < i then none else F j

/-- The file at `i` removed (an install's rename). -/
def releaseAt (F : Nat → Option BeImage) (i : Nat) : Nat → Option BeImage :=
  fun j => if j = i then none else F j

/-- `SaveDBFrom` of `img` at `i`: written unless a file for `i` is there already (`db.go:58`: the
new bytes are then discarded). -/
def saveAt (F : Nat → Option BeImage) (i : Nat) (img : BeImage) : Nat → Option BeImage :=
  fun j => if j = i then (match F i with | some b => some b | none => some img) else F j

/-- The files `F` had and `F'` has not, added to the removed images `H`. -/
def goneAdd (H : Nat → BeImage → Prop) (F F' : Nat → Option BeImage) : Nat → BeImage → Prop :=
  fun j img => H j img ∨ (F j = some img ∧ F' j = none)

/-- **What a crash leaves of the directory `F` with removed images `H`** (see the header). -/
def snapCrashed (F : Nat → Option BeImage) (H : Nat → BeImage → Prop) (F' : Nat → Option BeImage) :
    Prop :=
  ∀ j, F' j = F j ∨ (F j = none ∧ (F' j = none ∨ ∃ img, F' j = some img ∧ H j img))

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- The file at `path` is absent (`none`) or holds the image: 4a's `Backend.beFile`. -/
abbrev beFile (path : GoString) (o : Option BeImage) : IProp GF := Backend.beFile path o

/-- `ss` is a snapshotter of directory `sd` (persistent). -/
opaque isSnapshotter [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ss : Loc) (sd : GoString) : IProp GF := iprop(True)

/-- **The database snapshots in `sd` are `F`** (exclusive). -/
opaque snapDbs [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (sd : GoString) (F : Nat → Option BeImage) : IProp GF := iprop(True)

/-- **A save of `img` at `i` is between its rename and its directory fsync, over `F`** (exclusive). -/
opaque snapSaving [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (sd : GoString) (F : Nat → Option BeImage) (i : Nat) (img : BeImage) : IProp GF := iprop(True)

/-- **The images removed from `sd`'s db files that a crash may bring back** (exclusive). -/
opaque snapGone [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (sd : GoString) (H : Nat → BeImage → Prop) : IProp GF := iprop(True)

/-- **Provisional (batch 2f):** the reader `r` yields `img`'s bytes, then `EOF`, or fails. -/
opaque dbReader [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : GoInterface) (img : BeImage) : IProp GF := iprop(True)

/-- **Provisional (Perennial's `io`):** `rc.Close()` may be called once. -/
opaque rcClose [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rc : GoInterface) : IProp GF := iprop(True)

/-- `p` is a `*snap.Message` to member `to` of total size `sz` (persistent). -/
opaque isMessage [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (to : w64) (sz : w64) : IProp GF := iprop(True)

/-- The right to close `p`'s reader once (`CloseWithError`). -/
opaque msgClose [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) : IProp GF := iprop(True)

/-- `ch` is `p`'s close-notification channel (persistent): it receives one `bool`, after
`CloseWithError` (whether the reader closed without an error). -/
opaque msgCloseCh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (ch : Loc) : IProp GF := iprop(True)

def msgCloseCh_persistent.spec : Prop := ∀ p ch, Persistent (msgCloseCh (GF := GF) p ch)

def isSnapshotter_persistent.spec : Prop := ∀ ss sd, Persistent (isSnapshotter (GF := GF) ss sd)

def snapDbs_timeless.spec : Prop := ∀ sd F, Timeless (snapDbs (GF := GF) sd F)

def snapDbs_excl.spec : Prop := ∀ sd F F',
  snapDbs (GF := GF) sd F ∗ snapDbs sd F' ⊢ iprop(False)

def snapSaving_timeless.spec : Prop := ∀ sd F i img, Timeless (snapSaving (GF := GF) sd F i img)

/-- One directory view: at rest or in one save. -/
def snapSaving_excl.spec : Prop :=
  (∀ sd F F' i i' img img',
    snapSaving (GF := GF) sd F i img ∗ snapSaving sd F' i' img' ⊢ iprop(False)) ∧
  (∀ sd F F' i img, snapSaving (GF := GF) sd F i img ∗ snapDbs sd F' ⊢ iprop(False))

def snapGone_timeless.spec : Prop := ∀ sd H, Timeless (snapGone (GF := GF) sd H)

def snapGone_excl.spec : Prop := ∀ sd H H',
  snapGone (GF := GF) sd H ∗ snapGone sd H' ⊢ iprop(False)

def isMessage_persistent.spec : Prop := ∀ p to sz, Persistent (isMessage (GF := GF) p to sz)

/-- **A crash of the directory at rest** (trusted; see the header, "Crashes"): the next generation
`L'` finds a directory `snapCrashed` allows. -/
def snapDbs_crash.spec : Prop := ∀ (L' : GooseLocalGS GF) (sd : GoString)
    (F : Nat → Option BeImage) (H : Nat → BeImage → Prop),
  snapDbs (GF := GF) sd F ∗ snapGone sd H ∗ crashed ⊢
    |==> ∃ F', ⌜snapCrashed F H F'⌝ ∗ @snapDbs _ _ _ GF ⟨hG.goose_globalGS, L'⟩ sd F' ∗
      @snapGone _ _ _ GF ⟨hG.goose_globalGS, L'⟩ sd H

/-- **A crash during a save** (trusted): as at rest, the file at `i` possibly the new image. -/
def snapSaving_crash.spec : Prop := ∀ (L' : GooseLocalGS GF) (sd : GoString)
    (F : Nat → Option BeImage) (i : Nat) (img : BeImage) (H : Nat → BeImage → Prop),
  snapSaving (GF := GF) sd F i img ∗ snapGone sd H ∗ crashed ⊢
    |==> ∃ F', ⌜snapCrashed F H F' ∨ snapCrashed (saveAt F i img) H F'⌝ ∗
      @snapDbs _ _ _ GF ⟨hG.goose_globalGS, L'⟩ sd F' ∗
      @snapGone _ _ _ GF ⟨hG.goose_globalGS, L'⟩ sd H

end res

section rename
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The revert state of `p`, as the list of the files a crash may bring back** (re-review N3: two
installs with no directory sync between are reachable, `raft.go:284,307`, and a journaling file
system may then keep either rename or neither: every previous file is a candidate): 4a's
`Backend.beRevs p os` (`[]`: no rename pending, `beNoRevert`; else `beRevertL p os`). Verify round,
crash pass: the list form landed in 4a (`Durable.lean`'s `beRevs`, `beCrash`'s `o ∈ os`), so a
second install before a directory sync is provable (the transitional `False` for two or more is
gone). -/
abbrev revertSt (p : GoString) (os : List (Option BeImage)) : IProp GF := Backend.beRevs p os

/-- **Renaming a db file onto a backend path** (re-review N3: the destination's file and revert
state are taken inside the atomic update, so the install holds nothing across the call, a
concurrent `SaveDBFrom` can settle the revert state, and a crash in the call finds them in the
client's invariant) (trusted: `os.Rename` at the snapshotter's files,
whose meaning is `snapDbs`; the bridge from `os.Rename` to this model that `OpenSnapshotBackend`'s
proof needs: verify-round, A8 provability F5). At the rename the file at `i` leaves the directory
(the update reads it: `none` if it is not there, then `ENOENT` and nothing changes) and its image
is the destination's file; the removal is recorded in `snapGone`; the rename is not durable until
the directory is fsynced: the destination's previous file `o` may come back after a crash
(`revertSt dst (o :: os)`, 4a's `beCrash`/`beFile_crash`), until `SaveDBFrom`'s directory fsync. A failure other
than a missing file is `ServerStorage.diskOk`'s (`applySnapshot` panics on it, `bootstrap` fails).
Changes (second crash pass, G-b of `verify/F-server-boot.md`): the destination may be **open**
(`Backend.FileSt.opened γ L`: `applySnapshot` renames onto the backend's path while the old backend
is open, `server.go:1068` vs `:1144`; `bootstrap`'s recovery closes it first): `os.Rename` replaces
the directory entry, and the open handle keeps the old inode's bytes until its `Close`; the update
then gives the old backend's history back with `Backend.beDetached γ dst`
(`Backend.beRenamedOver`), whose entry joins the revert list at its close or at a crash. And the
renamed file `beFile dst (some img)` goes into the caller's state at the rename, not into the post
(it was in the post, while `OpenSnapshotBackend`'s update, since repair3-boot, puts it in its
client's state at the commit: a crash between the rename and the return found it in neither). -/
def dbFile_rename.spec : Prop :=
  ∀ (sd : GoString) (i : Nat) (dst : GoString) (Q : Option BeImage → IProp GF),
  {{ ⌜ServerStorage.diskOk⌝ ∗
      (AU <{ ∃∃ (F : Nat → Option BeImage) (H : Nat → BeImage → Prop) (d : Backend.FileSt)
                (os : List (Option BeImage)),
              snapDbs sd F ∗ snapGone sd H ∗ Backend.beAt dst d ∗ revertSt dst os }> @ ⊤, ∅
        <{ snapDbs sd (releaseAt F i) ∗ snapGone sd (goneAdd H F (releaseAt F i)) ∗
            (match F i with
             | some img => beFile dst (some img) ∗ Backend.beRenamedOver dst os d
             | none => Backend.beAt dst d ∗ revertSt dst os), COMM Q (F i) }>) }}
    (App (App (Val (@! os.Rename)) (Val #(dbPathOf sd i))) (Val #dst))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ img, Q (some img)) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ Q none) }}

end rename

end Snap
end EtcdGrove
end Perennial
