/-
# The server's storage (`server/storage`): vocabulary (batch 2e)

What the server needs of its storage package: the WAL behind the `Storage` interface the raft loop
writes (`storage.go`), the backend's opening (`backend.go`), the backend's commit hooks
(`hooks.go`), the quota (`quota.go`). Translated names only but the hooks and
`OpenSnapshotBackend`: the other specs are trusted, each stating what the Go code computes over
the WAL's model (`storage/wal/Api.lean`) and the snapshotter's (`etcdserver/api/snap/Api.lean`).

## Vocabulary

* `diskOk` (opaque `Prop`): **the environment premise**: the disk operations etcd treats as fatal
  or panics on succeed (creating, opening, reading, repairing and writing the WAL and fsyncing it,
  creating the snapshot directory, opening a bbolt file in `OpenBackend`'s goroutine, which panics
  in `backend.New` otherwise). Not a universal claim about disks: the adequacy theorem of a program
  carries it as its premise (the memory note "closed theorems: no panics", the user's 2026-11-08:
  "add an assumption that the backend opening doesn't panic"). Every operation below whose Go code
  would panic or exit on such a failure takes it; one that returns the error to a caller that
  handles it does not.
* `beOpen be path img` (exclusive): **provisional, batch 4a's**: `be` is an open backend of the
  file at `path`, which held `img` when it was opened; its `Close` gives `Snap.beFile path (some
  img')` back for the image `img'` of its last commit (4a's closer).
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
`beOpen_excl`.

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

/-- **The environment premise** (see the header). -/
opaque diskOk : Prop

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **Provisional (batch 4a):** `be` is an open backend of the file at `path`, which held `img`
when it was opened (exclusive). -/
opaque beOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (be : GoInterface) (path : GoString) (img : Snap.BeImage) : IProp GF := iprop(True)

/-- **Provisional (batch 4a):** `be`'s read-only operations (`Size`, `SizeInUse`: atomic reads) may
be called at any time, also after its close (persistent). -/
opaque beReadable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (be : GoInterface) : IProp GF := iprop(True)

/-- **Provisional (batch 4a):** `tx` is the backend's batch transaction, locked by the committing
goroutine, writable (exclusive). -/
opaque beTx [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tx : GoInterface) : IProp GF := iprop(True)

/-- `s` is a `*storage` over a WAL writing to `wd` and the snapshotter of `sd` (persistent). -/
opaque isStorage [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (wd sd : GoString) : IProp GF := iprop(True)

/-- `s` is not closed (fractional). -/
opaque storageOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (q : Qp) : IProp GF := iprop(True)

/-- The `Storage` interface value of `s`. -/
def storageIface (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #s

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
