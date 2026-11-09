/-
# etcd's backend meets mvcc's storage contract (batch 4a, for 3e and the server)

mvcc states its store over its own storage contract (`Mvcc.keyBackend B Pk`, `ApiStorage.lean`; the
user, 2026-11-06: "mvcc should respect the abstractions it builds on"); the server, which opens
etcd's backend and hands it to mvcc, discharges the contract through the law here. Only the server's
proofs import this module (mvcc never does).

## mvcc's part of the image

`mvccFp`: the `key` bucket (its existence, entries, buffer flag) and `meta`'s two compaction keys.
`meta`'s existence is mvcc's or not (`mvccFpM m`): the server creates `meta` before `mvcc.New`
(`bootstrap.go:266`) and freezes it (`beMade`: `m = true`, footprint `mvccFp`); `examples/mvccrand`
(`mvccrand.go:809-811`) hands `mvcc.New` a fresh backend, whose `NewStore` creates `meta` itself
under its lock (`kvstore.go:121-123`): then `meta`'s existence cell is mvcc's too (`m = false`,
footprint `mvccFp ∪ Fp.bkt metaBkt`; verify-round, A10-completeness F2, the mvcc group's request).
`keyDataOfM m V`: mvcc's `KeyData` read off a visible (or batch) image (`metaMade` true when frozen,
else the image's; `keyDataOf V = keyDataOfM true V`).
`schemaBkts`: the schema's buckets as the backend's declared set (`New`'s `Bs`; `schemaBkts_ok`).

## The law

`keyBackend_intro`: from the opener's resources on mvcc's part `mvccFpM m` (its batch and visible
images, equal outside a session; the delete right; `mvccReaderN` slots; an open share (`q` in the
statement, `q0` below); `meta` made when `m`; mvcc's
part disjoint from the hooks' cells) and the schema's buckets as the backend's (4b's `bucketAt` gives
`bucketOk`, `New`'s `Bs` gives `beBkt`), a storage `B` whose value is the backend: the contract at the
batch lock's `Pk`, mvcc's data at the visible image, the delete right, the slots, the whole open share
(`kbOpen B 1`, standing for `beOpen γ q0`), the hook and the commit request identified, the lent lock
(lendable to the lessor's write of cells mvcc does not track, and back), and the way back.

Intended realization (`q0` the share handed over; `B`'s names hold `γ`, `q0` and a ghost cell `γB`):
(`Fm := mvccFpM m` below.)
* `kbData B D := ∃ V, beVis γ Fm V ∗ ⌜D = keyDataOfM m V⌝ ∗ ((∃ C, beCur γ Fm C ∗ ⌜Image.agree
  Fm C V⌝) ∨ (lockTok γB ∗ beTurn γ))` (between sessions the batch part is here; a session takes it
  out at its lock's observation, leaving a token **and the session's turn** (verify-round,
  A10-provability B1), and puts it back at its `Unlock`'s second update, whose atomic precondition
  takes the turn from here in the same step). The lock rows close so: the new session's `Lock*`
  gave a turn, so `kbData`'s parked case is refuted by `beTurn_excl` (no session begins before the
  previous one's second update fired), and the observation finds `beCur` in `kbData`;
* `kbLocked B q D0 D := ∃ S C, beSess γ (q * q0) Fm S ∗ beCur γ Fm C ∗ lockTok' γB q ∗
  ⌜D0 = keyDataOfM m S.base ∧ D = keyDataCur m S C⌝` (the session widened to `Fm` at the lock,
  `beSess_widen` of `Fp.none`; `keyDataCur m S C`: `C`'s data, the buffer flag `S.base`'s cleared by a put
  of `key`, as `Sess.mid`'s; so `KeyData.mid D0 D = keyDataOf S.mid` for a session that deleted no
  `key` it put, the delete row's premise (b), and `D = keyDataOf S.fin`);
* `kbOpen B q := beOpen γ (q * q0) ∗ fracTok γB q` (a bridge-owned fraction, of which `kbLocked`
  holds its `q` with `lockTok'`: the way back's whole `kbOpen B 1` excludes an outstanding
  `kbLocked`, so `kbData` is in its batch case there: A10-provability B1's second part); `kbLive B t p := beLive γ (loc t) p` (`btLoc γ`, `rtLoc γ`, a
  concurrent one's `l`); `kbRead B rt D := ∃ V, beRd γ (loc rt) mvccFp V ∗ ⌜D = keyDataOf V⌝`;
  `kbRdToks B n := beRdToks γ n`; `kbBareSlot B := beRdToks γ 1`, `kbBare B := ∃ V, beRd γ (rtLoc γ)
  Fp.none V ∗ beLive γ (rtLoc γ) 1`; `kbSafe B := beDel γ`; `kbSafeHeld B := beDelHeld γ`;
  `kbMade B b := beMade γ b.name ∨ madeFlag γB b` (`key`, and `meta` when `m = false`: a monotone
bridge flag set when the bucket is created in mvcc's part, which no row drops; `meta` when `m`: the
server's `beMade`);
  `storageHook B dq f := beHook γ dq f`; `storageReq B Pk X Y := beReq γ Pk X Y`;
  `kbLent B H := □ (H -∗ ∃ q S, beSess γ q Fp.none S ∗ (beSess γ q Fp.none S -∗ H))` (the hook's
  session, 4a's (g), integration Y: so mvcc's `hookRun B Pk f Pre Q` gives 4a's `hookRun γ q Pk f Pre
  Q` at `H := beSess γ (q * q0) Fp.none S`, and a hook proved over 4a's `hookRun` at every share gives
  mvcc's: the hook conversion, a conjunct of the law's post); `mvccOn γ B` (persistent): a ghost record of the pair, in a global
  map from the backend's names (one storage per backend: `keyBackend_intro` takes `beDel γ`);
* `kbHeld B := ∃ q S, beSess γ q Fm S ∗ beLive γ (btLoc γ) 1 ∗ ⌜…⌝`, lent from `kbLocked` (with
  the session's liveness, `kbLocked_held`: the schema's `btView` holds it) with `lockTok'`'s other half
  (so the way back recovers the same share and a session that agrees with `S` on mvcc's cells:
  `heldBack`).

The rows, one by one: `BatchTx`/`ReadTx` (`backend.BatchTx.spec`, `ReadTx.spec`); the lock rows
(`batchTxBuffered.LockInsideApply`/`LockOutsideApply.spec` on `beOpen γ (q * q0)`; mvcc's `hookRun B`
gives 4a's `hookRun γ (q * q0) Pk f Pre Q` at `H` the session, `kbLent B H` by its realization (the
identity lend); the observation fired
after the lock with `beSess_vis`, `beSess_cur`); `Unlock` (`batchTxBuffered.Unlock.spec`, its two
updates mvcc's nested ones through `kbData`'s realization: `keyDataOf S.mid = KeyData.mid D0 D` needs
the delete row's (b), `beOpen` back as `kbOpen B q`); the puts (`UnsafePut`/`UnsafeSeqPut.spec`:
`Sess.fresh` from the row's freshness over `D0`, `D`; the entry bound `kbEntryMax = bboltEntryMax`;
`writable` by `mvccFp`); the delete (`UnsafeDelete.spec`, `beDelHeld`); `UnsafeCreateBucket` (`key`:
the `some (Fm, C)` case; `meta`: `none`, `beMade`, when `m`, else the `some (Fm, C)` case, setting
the bridge's `madeFlag`); the batch range (`btRange` is `KeyData.range`;
the bytes lent against `beLive`, as `kbLive`); `ConcurrentReadTx` (`beHookFp`, `Fp.disj mvccFp Fh`) and
its single-key range (`lingerSingle` is `KeyData.linger`, `mvccFp` covers the key); the shared
`RLock`/`RUnlock`/range (`rdRange` with `key` safe, `Fh` none of `key`'s cells: the plain cut when
`clean`, `A.take m ++ B.take n` otherwise, which is `KeyData.rtRange`'s `cs.take … ++ bs`; slices'
lengths below `2^63`); the bare lock rows (`readTx.RLock` with `Fp.none`, no `beOpen`: after the
close too); `ForceCommit` (`backend.ForceCommit.spec`); the safe-range lock; `Size`/`SizeInUse`/
`OpenReadTxN`.

4a's round-1 (g), lending the hook the session, is taken (integration Y): mvcc's `hookRun B` names
the storage and lends `kbLent B H`. The server proves its hook once, over 4a's `hookRun γ q Pk f Pre Q`
at every share (its `UnsafeConsistentIndex` reads through `beSess_rd`), and turns it into mvcc's by
this law's hook conversion (a conjunct of its post), into the lessor's by `LeaseBackend.lean`'s
`leaseHookRun_intro`, into
the schema's by `SchemaTx.lean`'s `applyHook_intro`. The rows rest on 4a's backend specs as they now
are; their own realization over 4c reads the bytes a range returned while the session writes (the
compaction deletes the keys its range returned): 4c's liveness token `Bbolt.txLive` (integration Y),
against whose share `txBytes_acc` lends, so `Bucket.Delete` keeps its `boltTx … 1`.
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

/-- **mvcc's part, `meta`'s existence included unless frozen** (`m`: `meta` made for good, the
server's `beMade`). -/
def mvccFpM (m : Bool) : Fp := if m then mvccFp else Fp.union mvccFp (Fp.bkt metaBkt)

/-- **mvcc's data read off an image** (`m`: `meta` made for good, the server's; else the image's). -/
def keyDataOfM (m : Bool) (V : Image) : Mvcc.KeyData :=
  { keyMade := V.made keyBkt, metaMade := m || V.made metaBkt, keys := V.ents keyBkt,
    sched := V.ents metaBkt (Mvcc.metaKey .sched), fin := V.ents metaBkt (Mvcc.metaKey .fin),
    clean := V.clean keyBkt }

/-- **mvcc's data read off an image with `meta` made** (the server's case). -/
def keyDataOf (V : Image) : Mvcc.KeyData := keyDataOfM true V

/-- **mvcc's data during a session `S` whose batch part is `C`**: `C`'s data, the `key` bucket's
buffer flag the session's base's, cleared by a put of `key` (as `Sess.mid`'s). -/
def keyDataCur (m : Bool) (S : Sess) (C : Image) : Mvcc.KeyData :=
  { keyDataOfM m C with clean := S.mid.clean keyBkt }

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
reader bound, in the backend's realization; mvcc's `mvccReaderN = mvccTokN + mvccOwnN + mvccRevN`
with `mvccTokN ≥ 2^28` and the `Rev` pool's `mvccRevN = 2^28` (integration Y), so mvcc's sealed
`mvccTokN` must stay below `2^30 - 2^28 - 2^27 - 6`: `2^28` fits). -/
def beReaderN_mvcc.spec : Prop := Mvcc.mvccReaderN + 2 ^ 27 ≤ beReaderN

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`B` is mvcc's storage over the backend `γ`** (persistent; `keyBackend_intro` gives it): what the
lessor's and the server's laws over both names take (`LeaseBackend.lean`). -/
opaque mvccOn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (B : Mvcc.MvccStorage) : IProp GF := iprop(True)

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def mvccOn_persistent.spec : Prop := ∀ γ B, Persistent (mvccOn (GF := GF) γ B)

/-- One storage per backend, one backend per storage, one storage per backend value. -/
def mvccOn_agree.spec : Prop := ∀ γ γ' B B',
  mvccOn (GF := GF) γ B ∗ mvccOn γ' B' ⊢
    ⌜(γ = γ' ↔ B = B') ∧ (Mvcc.storageVal B = Mvcc.storageVal B' → B = B')⌝

/-- **mvcc's storage value is the backend's** (with its batch lock's names). -/
def mvccOn_val.spec : Prop := ∀ γ B,
  mvccOn (GF := GF) γ B ⊢ ∃ b, ⌜GoInterface.ok (Mvcc.storageVal B) = beIface b⌝

/-- **The lent lock is mvcc's session** (as `keyBackend_intro`'s post; restated over `mvccOn` for the
lessor's `beTxHeld`, `LeaseBackend.lean`): lent to a writer of cells mvcc does not track, and given
back unchanged on mvcc's cells. -/
def mvccOn_held.spec : Prop := ∀ γ B,
  mvccOn (GF := GF) γ B ⊢ □ (Mvcc.kbHeld B -∗ ∃ (m : Bool) (q' : Qp) (S : Sess),
    beSess γ q' (mvccFpM m) S ∗ beLive γ (btLoc γ) 1 ∗
    ∀ S' : Sess, ⌜Sess.sameOn (mvccFpM m) S S'⌝ -∗ beSess γ q' (mvccFpM m) S' -∗
      beLive γ (btLoc γ) 1 -∗ Mvcc.kbHeld B)

/-- **etcd's backend is a storage for mvcc** (see the header): `m` whether `meta` is made for good
(the server's boot) or its existence is mvcc's too (a fresh backend, `examples/mvccrand`). -/
def keyBackend_intro.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (C V : Image) (q : Qp) (Fh : Fp)
    (m : Bool),
  isBackend γ b p Pk ∗
    (□ ∀ (bk : Schema.Bkt) (bv : GoInterface),
      Schema.bucketAt bk bv -∗ bkt γ bv ⟨bk.name, bk.id, bk.safe⟩) ∗
    beHookFp γ Fh ∗ ⌜Fp.disj (mvccFpM m) Fh⌝ ∗ (if m then beMade γ metaBkt else iprop(True)) ∗
    beCur γ (mvccFpM m) C ∗ beVis γ (mvccFpM m) V ∗ ⌜Image.agree (mvccFpM m) C V⌝ ∗
    beDel γ ∗ beRdToks γ Mvcc.mvccReaderN ∗ beOpen γ q
  ⊢ |={⊤}=> ∃ B : Mvcc.MvccStorage,
    ⌜GoInterface.ok (Mvcc.storageVal B) = beIface b⌝ ∗ Mvcc.keyBackend B Pk ∗
    Mvcc.kbData B (keyDataOfM m V) ∗ Mvcc.kbSafe B ∗ Mvcc.kbRdToks B Mvcc.mvccReaderN ∗
    Mvcc.kbOpen B 1 ∗ mvccOn γ B ∗
    (⌜m = true ∨ C.made metaBkt = true⌝ -∗ Mvcc.kbMade B .metaB) ∗
    (⌜C.made keyBkt = true⌝ -∗ Mvcc.kbMade B .keyB) ∗
    -- the hook and the commit request are the backend's
    □ (∀ dq f, Mvcc.storageHook B dq f ∗-∗ beHook γ dq f) ∗
    -- a hook proved over the backend's contract at every share is one over mvcc's (the hook conversion)
    □ (∀ (f : GoFunc) (Pre Q : IProp GF), (∀ q, hookRun γ q Pk f Pre Q) -∗ Mvcc.hookRun B Pk f Pre Q) ∗
    □ (∀ (X : IProp GF) (Y : IProp GF), beReq γ Pk X Y -∗ Mvcc.storageReq B Pk X Y) ∗
    -- the lent lock is mvcc's session, lent to a writer of cells mvcc does not track (the
    -- lessor's lease delete under mvcc's transaction) and given back unchanged on mvcc's cells
    □ (Mvcc.kbHeld B -∗ ∃ (q' : Qp) (S : Sess), beSess γ q' (mvccFpM m) S ∗ beLive γ (btLoc γ) 1 ∗
        ∀ S' : Sess, ⌜Sess.sameOn (mvccFpM m) S S'⌝ -∗ beSess γ q' (mvccFpM m) S' -∗
          beLive γ (btLoc γ) 1 -∗ Mvcc.kbHeld B) ∗
    -- the way back, for the backend's close: the trackers at mvcc's last data
    □ (∀ (n : Nat), Mvcc.storageRest B n ={⊤}=∗ ∃ (V' C' : Image),
        beVis γ (mvccFpM m) V' ∗ beCur γ (mvccFpM m) C' ∗ ⌜Image.agree (mvccFpM m) C' V'⌝ ∗
        beDel γ ∗ beRdToks γ n ∗ beOpen γ q)

end laws

end Backend
end EtcdGrove
end Perennial
