/-
# etcd's backend meets mvcc's storage contract (batch 4a, for 3e and the server)

mvcc states its store over its own storage contract (`Mvcc.keyBackend B Pk`, `ApiStorage.lean`; the
user, 2026-11-06: "mvcc should respect the abstractions it builds on"); the server, which opens
etcd's backend and hands it to mvcc, discharges the contract through the laws here. Only the
server's proofs import this module (mvcc never does).

## mvcc's part of the image

`mvccFp`: the `key` bucket (its existence, entries, buffer flag) and `meta`'s two compaction keys.
`meta`'s existence is not mvcc's: the server creates `meta` before `mvcc.New` (`bootstrap.go:266`)
and freezes it (`beMade`), so mvcc's view has it. `keyDataOf V`: mvcc's `KeyData` read off a visible
(or batch) image.

## The laws

* `keyBackend_intro`: from the opener's resources on mvcc's part (the batch and visible images on
  `mvccFp`, the delete right, `mvccReaderN` slots, `meta` made) and the schema's bucket values
  (`bucketOk` of `schema.Key`, `schema.Meta`: 4b's), a storage `B` whose value is the backend, with
  the contract at the batch lock's `Pk`, mvcc's data at the visible image, the delete right and the
  slots, the hook identified (`storageHook B dq f ⊣⊢ beHook γ dq f`), the commit request identified
  (`storageReq B Pk X Y` from `beReq γ Pk X Y`), the lent lock (`kbHeld B`: the session, for the
  lessor's untracked writes), and the way back (`storageRest B n` to the visible tracker and the
  delete right, which the backend's `Close` takes).
* `beReaderN_mvcc`: the slot stock covers mvcc's `mvccReaderN` with room for the other clients.
* Intended realization: `kbData B D := ∃ V, beVis γ mvccFp V ∗ ⌜D = keyDataOf V⌝`, `kbLocked B D :=
  ∃ q S, beSess γ q Fp.none S ∗ beCur γ mvccFp C ∗ ...` (mvcc's session widened to `mvccFp` at its
  `Unlock`), `kbRead B rt D := ∃ V, beRd γ rt mvccFp V ∗ ...`, `kbRdToks B n := beRdToks γ n`,
  `kbSafe B := beDel γ`, `kbMade B b := beMade γ (name b)`.

**Blocked on 3e's contract** (`notes/specs-only/batch-4a.md`, findings F1 and F3, and
`req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 4a"): the contract's `Unlock` row fires one
update, but etcd's backend shows a session's puts at the write-back and its deletes only at the
commit (`Sess.mid`): between the two, a reader sees `finishedCompactRev` set and the batch's
deleted `key` entries still there (the compaction's last batch, `kvstore_compaction.go:70-71`); and
the `key` put row requires the key above the batch's keys only, not above those the session deleted
and readers still see. The law below is stated against the contract as it is and is not provable
until those rows change.
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
def keyBkt : GoString := go!"key"

/-- The `meta` bucket's name (`schema.Meta`). -/
def metaBkt : GoString := go!"meta"

/-- **mvcc's part of the image**: the `key` bucket and `meta`'s compaction keys. -/
def mvccFp : Fp :=
  Fp.union (Fp.bucket keyBkt)
    (Fp.union (Fp.key metaBkt (Mvcc.metaKey .sched)) (Fp.key metaBkt (Mvcc.metaKey .fin)))

/-- **mvcc's data read off an image** (`meta` made: the server's). -/
def keyDataOf (V : Image) : Mvcc.KeyData :=
  { keyMade := V.made keyBkt, metaMade := true, keys := V.ents keyBkt,
    sched := V.ents metaBkt (Mvcc.metaKey .sched), fin := V.ents metaBkt (Mvcc.metaKey .fin),
    clean := V.clean keyBkt }

end model

/-- **The backend's reader slots cover mvcc's and leave room for its other clients** (auth, the
server's): an obligation on the two sealed constants (`beReaderN ≤ 2^30 - 2`, Go's `RWMutex`
reader bound, in the backend's realization; mvcc's `mvccReaderN = mvccTokN + mvccOwnN` with
`mvccTokN ≥ 2^28`, so mvcc's must stay below `2^30 - 2^28`). -/
def beReaderN_mvcc.spec : Prop := Mvcc.mvccReaderN + 2 ^ 27 ≤ beReaderN

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **etcd's backend is a storage for mvcc** (see the header; blocked on 3e's F1, F3). -/
def keyBackend_intro.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (C V : Image) (idk idm : w64),
  isBackend γ b p Pk ∗
    bucketOk (Mvcc.bucketVal .keyB) ⟨keyBkt, idk, true⟩ ∗
    bucketOk (Mvcc.bucketVal .metaB) ⟨metaBkt, idm, false⟩ ∗
    beMade γ metaBkt ∗ beCur γ mvccFp C ∗ beVis γ mvccFp V ∗ beDel γ ∗ beRdToks γ Mvcc.mvccReaderN
  ⊢ |={⊤}=> ∃ B : Mvcc.MvccStorage,
    ⌜GoInterface.ok (Mvcc.storageVal B) = beIface b⌝ ∗ Mvcc.keyBackend B Pk ∗
    Mvcc.kbData B (keyDataOf V) ∗ Mvcc.kbSafe B ∗ Mvcc.kbRdToks B Mvcc.mvccReaderN ∗
    Mvcc.kbMade B .metaB ∗ (⌜C.made keyBkt = true⌝ -∗ Mvcc.kbMade B .keyB) ∗
    -- the hook and the commit request are the backend's
    □ (∀ dq f, Mvcc.storageHook B dq f ∗-∗ beHook γ dq f) ∗
    □ (∀ (X : IProp GF) (Y : IProp GF), beReq γ Pk X Y -∗ Mvcc.storageReq B Pk X Y) ∗
    -- the lent lock is the session (the lessor's untracked writes under mvcc's transaction)
    □ (Mvcc.kbHeld B ∗-∗ ∃ q F S, beSess γ q F S) ∗
    -- the way back, for the backend's close
    □ (∀ n, Mvcc.storageRest B n ={⊤}=∗ ∃ V', beVis γ mvccFp V' ∗ beDel γ ∗ beRdToks γ n)

end laws

end Backend
end EtcdGrove
end Perennial
