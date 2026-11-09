/-
# etcd's backend meets mvcc's storage contract (batch 4a, for 3e and the server)

mvcc states its store over its own storage contract (`Mvcc.keyBackend B Pk`, `ApiStorage.lean`; the
user, 2026-11-06: "mvcc should respect the abstractions it builds on"); the server, which opens
etcd's backend and hands it to mvcc, discharges the contract through the law here. Only the server's
proofs import this module (mvcc never does).

## mvcc's part of the image

`mvccFp`: the `key` bucket (its existence, entries, buffer flag) and `meta`'s two compaction keys.
`meta`'s existence is not mvcc's: the server creates `meta` before `mvcc.New` (`bootstrap.go:266`)
and freezes it (`beMade`). `keyDataOf V`: mvcc's `KeyData` read off a visible (or batch) image.
`schemaBkts`: the schema's buckets as the backend's declared set (`New`'s `Bs`; `schemaBkts_ok`).

## The law

`keyBackend_intro`: from the opener's resources on mvcc's part (its batch and visible images, equal
outside a session; the delete right; `mvccReaderN` slots; an open share; `meta` made; mvcc's part
disjoint from the hooks' cells) and the schema's buckets as the backend's (4b's `bucketAt` gives
`bucketOk`, `New`'s `Bs` gives `beBkt`), a storage `B` whose value is the backend: the contract at the
batch lock's `Pk`, mvcc's data at the visible image, the delete right, the slots, the hook and the
commit request identified, the lent lock pinned to mvcc's footprint, and the way back.

Intended realization: `kbData B D := ∃ V, beVis γ mvccFp V ∗ ⌜D = keyDataOf V⌝`; `kbLocked B D0 D :=
∃ q S C, beSess γ q mvccFp S ∗ beCur γ mvccFp C ∗ ⌜D0 = keyDataOf S.base ∧ D = keyDataOf C⌝` (the
session widened to `mvccFp` at the lock, `beSess_widen`; `KeyData.mid D0 D` is `keyDataOf (Sess.mid
S)` as long as the session put no `key` it later deleted, mvcc's delete row's premise to add, item
(b) below; mvcc's nested update is `Unlock`'s two with `Ψ1 :=` the inner update);
`kbRead B rt D := ∃ V, beRd γ rt mvccFp V ∗ ⌜D = keyDataOf V⌝`; `kbRdToks B n := beRdToks γ n`;
`kbSafe B := beDel γ`; `kbMade B b := beMade γ (name b)`; `kbHeld B := ∃ q S, beSess γ q mvccFp S`.

**Blocked on 3e's contract** (`req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 4a, round 1"):
(a) an open share on the lock rows and `ForceCommit` (`ForceCommit` and a locked hook after the
close panic); (b) the `key` delete row's "not put in this session"; (c) the entry bound on the put
rows; (e) a concurrent read transaction's range row (single keys, lingering deletes: the stale
buffer copy); (f) the range rows' bytes lent, not for good. F1 and F3 (the two-step `Unlock`, the
freshness over the session's start) are taken by 3e's round 2.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section model
variable [GooseExts]

/-- The `key` bucket's name (`schema.Key`). -/
def keyBkt : GoString := Schema.Bkt.name .key

/-- The `meta` bucket's name (`schema.Meta`). -/
def metaBkt : GoString := Schema.Bkt.name .metaB

/-- **mvcc's part of the image**: the `key` bucket and `meta`'s compaction keys. -/
def mvccFp : Fp :=
  Fp.union (Fp.bucket keyBkt)
    (Fp.union (Fp.key metaBkt (Mvcc.metaKey .sched)) (Fp.key metaBkt (Mvcc.metaKey .fin)))

/-- **mvcc's data read off an image** (`meta` made: the server's). -/
def keyDataOf (V : Image) : Mvcc.KeyData :=
  { keyMade := V.made keyBkt, metaMade := true, keys := V.ents keyBkt,
    sched := V.ents metaBkt (Mvcc.metaKey .sched), fin := V.ents metaBkt (Mvcc.metaKey .fin),
    clean := V.clean keyBkt }

/-- **The schema's buckets as a declared set** (`New`'s `Bs`). -/
def schemaBkts (bi : BktInfo) : Prop :=
  ∃ b : Schema.Bkt, bi = ⟨b.name, b.id, b.safe⟩

end model

/-- The schema's buckets have distinct ids and names (an obligation on 4b's constants; true by
`Schema.Bkt.id`'s and `name`'s tables). -/
def schemaBkts_ok.spec [GooseExts] : Prop := bktsOk schemaBkts

/-- **The backend's reader slots cover mvcc's and leave room for its other clients** (auth, the
server's): an obligation on the two sealed constants (`beReaderN ≤ 2^30 - 2`, Go's `RWMutex`
reader bound, in the backend's realization; mvcc's `mvccReaderN = mvccTokN + mvccOwnN` with
`mvccTokN ≥ 2^28`, so mvcc's must stay below `2^30 - 2^28`). -/
def beReaderN_mvcc.spec : Prop := Mvcc.mvccReaderN + 2 ^ 27 ≤ beReaderN

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **etcd's backend is a storage for mvcc** (see the header; blocked on 3e's (a), (b), (c), (e),
(f)). -/
def keyBackend_intro.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (C V : Image) (q : Qp) (Fh : Fp),
  isBackend γ b p Pk ∗
    (□ ∀ (bk : Schema.Bkt) (bv : GoInterface),
      Schema.bucketAt bk bv -∗ bkt γ bv ⟨bk.name, bk.id, bk.safe⟩) ∗
    beHookFp γ Fh ∗ ⌜Fp.disj mvccFp Fh⌝ ∗ beMade γ metaBkt ∗
    beCur γ mvccFp C ∗ beVis γ mvccFp V ∗ ⌜Image.agree mvccFp C V⌝ ∗
    beDel γ ∗ beRdToks γ Mvcc.mvccReaderN ∗ beOpen γ q
  ⊢ |={⊤}=> ∃ B : Mvcc.MvccStorage,
    ⌜GoInterface.ok (Mvcc.storageVal B) = beIface b⌝ ∗ Mvcc.keyBackend B Pk ∗
    Mvcc.kbData B (keyDataOf V) ∗ Mvcc.kbSafe B ∗ Mvcc.kbRdToks B Mvcc.mvccReaderN ∗
    Mvcc.kbMade B .metaB ∗ (⌜C.made keyBkt = true⌝ -∗ Mvcc.kbMade B .keyB) ∗
    -- the hook and the commit request are the backend's
    □ (∀ dq f, Mvcc.storageHook B dq f ∗-∗ beHook γ dq f) ∗
    □ (∀ (X : IProp GF) (Y : IProp GF), beReq γ Pk X Y -∗ Mvcc.storageReq B Pk X Y) ∗
    -- the lent lock is mvcc's session (the lessor's untracked writes under mvcc's transaction)
    □ (Mvcc.kbHeld B ∗-∗ ∃ (q' : Qp) (S : Sess), beSess γ q' mvccFp S) ∗
    -- the way back, for the backend's close: the trackers at mvcc's last data
    □ (∀ (n : Nat), Mvcc.storageRest B n ={⊤}=∗ ∃ (V' C' : Image),
        beVis γ mvccFp V' ∗ beCur γ mvccFp C' ∗ ⌜Image.agree mvccFp C' V'⌝ ∗
        beDel γ ∗ beRdToks γ n ∗ beOpen γ q)

end laws

end Backend
end EtcdGrove
end Perennial
