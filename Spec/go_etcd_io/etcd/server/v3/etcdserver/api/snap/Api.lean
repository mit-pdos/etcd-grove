/-
# The snapshotter (`etcdserver/api/snap`): vocabulary (batch 2e)

The snapshotter keeps the **database snapshots** a member received (`<snap dir>/<index:016x>.snap.db`:
a leader's backend, sent in a merged `MsgSnap`), until the apply thread installs one as the member's
backend (`serverstorage.OpenSnapshotBackend`: a rename onto the backend's path) or a later snapshot
releases it (`ReleaseSnapDBs`). The package is translated names only (but `Message.GetTo`); its
specs are trusted, each stating what the Go code computes (`db.go`, `snapshotter.go`, `message.go`).

## Vocabulary

* `BeImage` (4a's `Backend.Image` since integration X), `beFile path o` (exclusive, timeless): **provisional, batch 4a's**
  (`notes/specs-only/req/go_etcd_io_etcd_server_v3_storage_backend.md`, "from 2e"): what a bbolt
  database file holds, as the backend reads it after an open (`none`: no file at `path`). A
  snapshot db file, the backend's own file and the image a leader streams are all `BeImage`s, so a
  rename carries the image unchanged. At integration 4a's names replace these.
* `isSnapshotter ss sd` (persistent): `ss` is a `*Snapshotter` of directory `sd` (its fields
  read-only: the logger, the directory, the fsync function).
* `snapDbs sd F` (exclusive, timeless): **the database snapshots in `sd`**: `F i` is the image of
  `<sd>/<i:016x>.snap.db` (`none`: no such file). Intended realization: a ghost variable whose
  meaning ("what `os.Rename` of that file onto a path, then an open, reads") is trusted, as
  `Wal.walRecs`. Held by the server's invariant (the receiving transport adds, the apply thread
  installs and releases), by `EtcdServer.memberDisk` while the member is stopped.
* `dbReader r img` (exclusive): **provisional, batch 2f's**: the `io.Reader` `r` yields the bytes
  of `img` and then `EOF` (or fails: a cut stream). rafthttp's merged-snapshot reader is one.
* `isMessage p to sz` (persistent) and `msgClose p` (exclusive, once): a `*snap.Message` to member
  `to`, of total size `sz`, whose reader closes once (`CloseWithError`).
* `rcClose rc` (exclusive, once): **provisional, Perennial's `io`**: `rc.Close()` may be called
  once (the reader `NewMessage` wraps; the axiom sweep's B3-3: a nil reader panics at the close).

## Laws

`isSnapshotter_persistent`, `snapDbs_timeless`, `snapDbs_excl`, `beFile_timeless`, `beFile_excl`,
`isMessage_persistent`.

## Requirement snippets

`examples/specreq/etcdserverboot/snap.go` (`ReqSnapRoundTrip`: a received snapshot saved, found by
index, installed, older ones released).
-/
module

public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
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

/-- **Provisional (batch 4a):** `img` is the image of a new, empty database (bbolt creates the
file). -/
opaque emptyImage (img : BeImage) : Prop

/-- `ReleaseSnapDBs` at index `i`: the files of lower indices removed. -/
def releaseBelow (F : Nat → Option BeImage) (i : Nat) : Nat → Option BeImage :=
  fun j => if j < i then none else F j

/-- `SaveDBFrom` of `img` at `i`: written unless a file for `i` is there already (`db.go:58`: the
new bytes are then discarded). -/
def saveAt (F : Nat → Option BeImage) (i : Nat) (img : BeImage) : Nat → Option BeImage :=
  fun j => if j = i then (match F i with | some b => some b | none => some img) else F j

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- **Provisional (batch 4a):** the file at `path` is absent (`none`) or holds the image. -/
opaque beFile [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (path : GoString) (o : Option BeImage) : IProp GF := iprop(True)

/-- `ss` is a snapshotter of directory `sd` (persistent). -/
opaque isSnapshotter [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ss : Loc) (sd : GoString) : IProp GF := iprop(True)

/-- **The database snapshots in `sd` are `F`** (exclusive). -/
opaque snapDbs [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (sd : GoString) (F : Nat → Option BeImage) : IProp GF := iprop(True)

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

def beFile_timeless.spec : Prop := ∀ p o, Timeless (beFile (GF := GF) p o)

def beFile_excl.spec : Prop := ∀ p o o',
  beFile (GF := GF) p o ∗ beFile p o' ⊢ iprop(False)

def isMessage_persistent.spec : Prop := ∀ p to sz, Persistent (isMessage (GF := GF) p to sz)

end res

end Snap
end EtcdGrove
end Perennial
