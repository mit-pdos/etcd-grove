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
outside a session; the delete right; `mvccReaderN` slots; an open share (`q` in the statement,
`q0` below); `meta` made; mvcc's
part disjoint from the hooks' cells) and the schema's buckets as the backend's (4b's `bucketAt` gives
`bucketOk`, `New`'s `Bs` gives `beBkt`), a storage `B` whose value is the backend: the contract at the
batch lock's `Pk`, mvcc's data at the visible image, the delete right, the slots, the whole open share
(`kbOpen B 1`, standing for `beOpen γ q0`), the hook and the commit request identified, the lent lock
(lendable to the lessor's write of cells mvcc does not track, and back), and the way back.

Intended realization (`q0` the share handed over; `B`'s names hold `γ`, `q0` and a ghost cell `γB`):
* `kbData B D := ∃ V, beVis γ mvccFp V ∗ ⌜D = keyDataOf V⌝ ∗ (∃ C, beCur γ mvccFp C ∗ ⌜Image.agree
  mvccFp C V⌝ ∨ lockTok γB)` (between sessions the batch part is here; a session takes it out at its
  lock's observation, leaving a token, and puts it back at its `Unlock`'s second update);
* `kbLocked B q D0 D := ∃ S C, beSess γ (q * q0) mvccFp S ∗ beCur γ mvccFp C ∗ lockTok' γB ∗
  ⌜D0 = keyDataOf S.base ∧ D = keyDataCur S C⌝` (the session widened to `mvccFp` at the lock,
  `beSess_widen` of `Fp.none`; `keyDataCur S C`: `C`'s data, the buffer flag `S.base`'s cleared by a put
  of `key`, as `Sess.mid`'s; so `KeyData.mid D0 D = keyDataOf S.mid` for a session that deleted no
  `key` it put, the delete row's premise (b), and `D = keyDataOf S.fin`);
* `kbOpen B q := beOpen γ (q * q0)`; `kbLive B t p := beLive γ (loc t) p` (`btLoc γ`, `rtLoc γ`, a
  concurrent one's `l`); `kbRead B rt D := ∃ V, beRd γ (loc rt) mvccFp V ∗ ⌜D = keyDataOf V⌝`;
  `kbRdToks B n := beRdToks γ n`; `kbBareSlot B := beRdToks γ 1`, `kbBare B := ∃ V, beRd γ (rtLoc γ)
  Fp.none V ∗ beLive γ (rtLoc γ) 1`; `kbSafe B := beDel γ`; `kbSafeHeld B := beDelHeld γ`;
  `kbMade B b := beMade γ b.name` (`key`: by `beCur_freeze` once created; `meta`: the server's);
  `storageHook B dq f := beHook γ dq f`; `storageReq B Pk X Y := beReq γ Pk X Y`;
* `kbHeld B := ∃ q S, beSess γ q mvccFp S ∗ ⌜…⌝`, lent from `kbLocked` with `lockTok'`'s other half
  (so the way back recovers the same share and a session that agrees with `S` on mvcc's cells:
  `heldBack`).

The rows, one by one: `BatchTx`/`ReadTx` (`backend.BatchTx.spec`, `ReadTx.spec`); the lock rows
(`batchTxBuffered.LockInsideApply`/`LockOutsideApply.spec` on `beOpen γ (q * q0)`; mvcc's `hookRun`
gives 4a's `hookRun γ q Pk f Pre Q` by framing the session around the hook; the observation fired
after the lock with `beSess_vis`, `beSess_cur`); `Unlock` (`batchTxBuffered.Unlock.spec`, its two
updates mvcc's nested ones through `kbData`'s realization: `keyDataOf S.mid = KeyData.mid D0 D` needs
the delete row's (b), `beOpen` back as `kbOpen B q`); the puts (`UnsafePut`/`UnsafeSeqPut.spec`:
`Sess.fresh` from the row's freshness over `D0`, `D`; the entry bound `kbEntryMax = bboltEntryMax`;
`writable` by `mvccFp`); the delete (`UnsafeDelete.spec`, `beDelHeld`); `UnsafeCreateBucket` (`key`:
the `some (mvccFp, C)` case; `meta`: `none`, `beMade`); the batch range (`btRange` is `KeyData.range`;
the bytes lent against `beLive`, as `kbLive`); `ConcurrentReadTx` (`beHookFp`, `Fp.disj mvccFp Fh`) and
its single-key range (`lingerSingle` is `KeyData.linger`, `mvccFp` covers the key); the shared
`RLock`/`RUnlock`/range (`rdRange` with `key` safe, `Fh` none of `key`'s cells: the plain cut when
`clean`, `A.take m ++ B.take n` otherwise, which is `KeyData.rtRange`'s `cs.take … ++ bs`; slices'
lengths below `2^63`); the bare lock rows (`readTx.RLock` with `Fp.none`, no `beOpen`: after the
close too); `ForceCommit` (`backend.ForceCommit.spec`); the safe-range lock; `Size`/`SizeInUse`/
`OpenReadTxN`.

Not taken from 4a's round-1 list: (g), lending the hook the session (`hookRun` would need the
storage as an argument; recorded in `notes/specs-only/integration-I6.md`). The rows rest on 4a's
backend specs as they now are; their own realization over 4c needs bbolt to read a key it returned
while deleting it (4c's `Bucket.Delete` takes `boltTx … 1` and a plain points-to: recorded).
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

/-- **mvcc's data during a session `S` whose batch part is `C`**: `C`'s data, the `key` bucket's
buffer flag the session's base's, cleared by a put of `key` (as `Sess.mid`'s). -/
def keyDataCur (S : Sess) (C : Image) : Mvcc.KeyData :=
  { keyDataOf C with clean := S.mid.clean keyBkt }

/-- **A session given back unchanged on `F`**: the same base, the same batch cells and puts of `F`
(a borrower of the lock wrote other cells only). -/
def Sess.sameOn (F : Fp) (S S' : Sess) : Prop :=
  S'.base = S.base ∧ Image.agree F S'.cur S.cur ∧ ∀ b k, F (.key b k) → S'.puts b k = S.puts b k

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

/-- **etcd's backend is a storage for mvcc** (see the header). -/
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
    Mvcc.kbOpen B 1 ∗
    Mvcc.kbMade B .metaB ∗ (⌜C.made keyBkt = true⌝ -∗ Mvcc.kbMade B .keyB) ∗
    -- the hook and the commit request are the backend's
    □ (∀ dq f, Mvcc.storageHook B dq f ∗-∗ beHook γ dq f) ∗
    □ (∀ (X : IProp GF) (Y : IProp GF), beReq γ Pk X Y -∗ Mvcc.storageReq B Pk X Y) ∗
    -- the lent lock is mvcc's session, lent to a writer of cells mvcc does not track (the
    -- lessor's lease delete under mvcc's transaction) and given back unchanged on mvcc's cells
    □ (Mvcc.kbHeld B -∗ ∃ (q' : Qp) (S : Sess), beSess γ q' mvccFp S ∗
        ∀ S' : Sess, ⌜Sess.sameOn mvccFp S S'⌝ -∗ beSess γ q' mvccFp S' -∗ Mvcc.kbHeld B) ∗
    -- the way back, for the backend's close: the trackers at mvcc's last data
    □ (∀ (n : Nat), Mvcc.storageRest B n ={⊤}=∗ ∃ (V' C' : Image),
        beVis γ mvccFp V' ∗ beCur γ mvccFp C' ∗ ⌜Image.agree mvccFp C' V'⌝ ∗
        beDel γ ∗ beRdToks γ n ∗ beOpen γ q)

end laws

end Backend
end EtcdGrove
end Perennial
