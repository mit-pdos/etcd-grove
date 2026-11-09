/-
# The server's storage (`server/storage`): vocabulary (batch 2e)

What the server needs of its storage package: the WAL behind the `Storage` interface the raft loop
writes (`storage.go`), the backend's opening (`backend.go`), the backend's commit hooks
(`hooks.go`), the quota (`quota.go`). Translated names only but the hooks and
`OpenSnapshotBackend`: the other specs are trusted, each stating what the Go code computes over
the WAL's model (`storage/wal/Api.lean`) and the snapshotter's (`etcdserver/api/snap/Api.lean`).

## Vocabulary

* `diskOk` (opaque `Prop`, declared in `storage/wal/Api.lean` below the WAL's crash laws that take
  it): **the environment premise**. Its text is its meaning, and it names every failure it
  excludes (verify-round, A8 provability F7). The disk operations below succeed:
  - the WAL's: creating, opening, reading (`ReadAll`), repairing, writing and fsyncing it, cutting a
    segment, `Sync`, `Close`'s fsync (an error is returned and the raft loop or `bootstrap` exits);
  - **after a crash**, the WAL's files hold a prefix of the records written, each record whole or
    torn only at the tail (no record behind a surviving one corrupted, no garbage passing the CRC
    chain): otherwise `ReadAll` fails with `ErrCRCMismatch` and `bootstrap` exits. Among them
    (verify round, crash pass: R-A8 S2) **a torn tail with no all-zero sector**: OsFs's power loss
    leaves a dirty byte arbitrary, and `decoder.go`'s `isTornEntry` recognizes a torn tail only by
    a zeroed sector, reporting `ErrCRCMismatch` otherwise. The WAL's crash laws
    (`Wal.walRecs_crash`, `walWriting_crash`) take it;
  - the snapshot directory's: creating it; `DBFilePath`'s `ReadDir`; `ReleaseSnapDBs`' `os.Open`
    and `Readdirnames` of it and each `os.Remove` of a db file below the index (a failure other than
    a missing file is only logged); `SaveDBFrom`'s fsync of the directory after its rename, or when
    the file is already there (the Go code returns that error to rafthttp's handler; excluded so
    that a returned error means nothing changed);
  - the install's `os.Rename` of a db file onto the backend's path (`Snap.dbFile_rename`; a missing
    source is not a failure here: it is the spec's `none` arm), which `applySnapshot` panics on;
  - opening the bbolt file in `OpenBackend`'s goroutine: 4a's `Backend.dbOpenOk` of the
    `BackendConfig` `newBackend` builds (`backend.New` panics otherwise).
  Not a universal claim about disks: the adequacy theorem of a program carries it as its premise
  (the memory note "closed theorems: no panics", the user's 2026-11-08: "add an assumption that the
  backend opening doesn't panic"). Every operation below whose Go code would panic or exit on such
  a failure takes it; one that returns the error to a caller that handles it does not (but
  `SaveDBFrom`'s directory fsync, above).
* The backend: 4a's vocabulary (`Backend.isBackend`, `beFile`, `New.spec`'s allocation step), which
  `OpenBackend`/`OpenSnapshotBackend` now return (verify-round, A8 provability F5). `beOpen be path
  img` (exclusive) is **superseded**: no spec here takes or gives it any more; it stays declared
  only until the server's specs that still mention it (`bootstrap`, `applySnapshot`, the
  `bootstrapped*.Close` specs: server-core's) move to 4a's names, then goes. `beReadable be`
  (persistent, `Size`/`SizeInUse` at any time) is still provisional (4a's `backend__Size`'s shape:
  open); `beTx tx` is superseded by 4a's `hookOk` (`BackendHooks.OnPreCommitUnsafe.spec`, over
  `hooksPkOk` and `hookFp`).
* `hooksIface h`: the `backend.Hooks` interface value of the hooks `h`.
* `isStorage s wd sd` (persistent): `s` is a `*storage` over a WAL writing to `wd` and the
  snapshotter of `sd`. Intended realization: the `RWMutex`'s invariant holding `Wal.walOpen w wd`
  (until `Close`) and `s.w ↦ w`, read-only `lg`, `s.s` (`Snap.isSnapshotter`).
* `storageOpen s q` (fractional): `s` is not closed; `Close` takes all of it. The raft loop holds a
  share, the apply thread's `snapshot` another (it calls `SaveSnap` and `Release` concurrently).
* `storageIface s`: the `Storage` interface value of `s` (the dynamic type `*storage` is tracked:
  `NewStorage`'s caller, `bootstrappedRaft.newRaftNode`, hands it to the raft node, whose spec
  (2d) calls the concrete methods' specs below).
* `isHooks h ci` (persistent): `h` is a `*BackendHooks` over the consistent indexer `ci` (2d's
  `cindex`), its pending configuration under its lock.
* `isQuota q` (persistent): `q` is a `Quota` (`*BackendQuota` or `*passthroughQuota`) over an open
  backend. `quotaReq v dq`: `v` is one of the three requests `Cost` accepts (`Cost` panics on any
  other: `quota.go:138`), readable at `dq`.

## Laws

`isStorage_persistent`, `storageOpen_fractional`, `isHooks_persistent`, `isQuota_persistent`,
`beOpen_excl` (superseded with `beOpen`).

## Requirement snippets

`examples/specreq/etcdserverboot/storage.go` (the raft loop's write order: `SaveSnap` before `Save`
of a received snapshot, `Release` only of a saved snapshot; the quota's three request kinds).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import Spec.go_etcd_io.etcd.api.v3.Wire
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.storage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ServerStorage

open Iris Iris.BI

-- `diskOk` (the environment premise, see the header) is declared in `storage/wal/Api.lean`, whose
-- crash laws take it.

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **Superseded (verify-round, A8 provability F5)** by 4a's `Backend.isBackend` (what
`OpenBackend.spec` now returns); kept only until the server's specs that mention it move. -/
opaque beOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (be : GoInterface) (path : GoString) (img : Snap.BeImage) : IProp GF := iprop(True)

/-- **Provisional (batch 4a):** `be`'s read-only operations (`Size`, `SizeInUse`: atomic reads) may
be called at any time, also after its close (persistent). -/
opaque beReadable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (be : GoInterface) : IProp GF := iprop(True)

/-- **Superseded (last pass)**: the hooks' spec is now 4a's `hookOk` (`BackendHooks.OnPreCommitUnsafe.spec`);
no spec uses `beTx`. -/
opaque beTx [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tx : GoInterface) : IProp GF := iprop(True)

/-- `s` is a `*storage` over a WAL writing to `wd` and the snapshotter of `sd` (persistent). -/
opaque isStorage [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (wd sd : GoString) : IProp GF := iprop(True)

/-- `s` is not closed (fractional). -/
opaque storageOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (q : Qp) : IProp GF := iprop(True)

/-- The `Storage` interface value of `s`. -/
def storageIface (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #s

/-- The `backend.Hooks` interface value of the hooks `h`. -/
def hooksIface (h : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty) #h

/-- `h` is a `*BackendHooks` over the consistent indexer `ci` (persistent). -/
opaque isHooks [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (h : Loc) (ci : GoInterface) : IProp GF := iprop(True)

/-- `q` is a `Quota` (persistent). -/
opaque isQuota [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (q : GoInterface) : IProp GF := iprop(True)

/-- `v` is a request `Cost` accepts: a `*PutRequest` or a `*TxnRequest` readable at `dq`, or a
`*LeaseGrantRequest`. -/
def quotaReq (v : GoInterface) (dq : DFrac) : IProp GF :=
  iprop((∃ (p : Loc) (r : EtcdModel.PutReq),
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.PutRequest.ty) #p⌝ ∗
      EtcdWire.putReqOwn p dq r) ∨
    (∃ (p : Loc) (t : EtcdModel.TxnReq),
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.TxnRequest.ty) #p⌝ ∗
      EtcdWire.txnReqOwn p dq t) ∨
    (∃ p : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantRequest.ty) #p⌝))

def isStorage_persistent.spec : Prop := ∀ s wd sd, Persistent (isStorage (GF := GF) s wd sd)

def storageOpen_fractional.spec : Prop := ∀ s (q₁ q₂ : Qp),
  storageOpen (GF := GF) s (q₁ + q₂) ⊣⊢ storageOpen s q₁ ∗ storageOpen s q₂

def isHooks_persistent.spec : Prop := ∀ h ci, Persistent (isHooks (GF := GF) h ci)

def isQuota_persistent.spec : Prop := ∀ q, Persistent (isQuota (GF := GF) q)

def beOpen_excl.spec : Prop := ∀ be be' path img img',
  beOpen (GF := GF) be path img ∗ beOpen be' path img' ⊢ iprop(False)

end res

end ServerStorage
end EtcdGrove
end Perennial
