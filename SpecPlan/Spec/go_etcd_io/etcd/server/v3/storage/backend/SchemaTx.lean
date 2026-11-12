/-
# etcd's backend meets the schema's transaction contracts (integration of 4a and 4b)

The schema (`storage/schema/Api.lean`, 4b) is stated over what it needs of a transaction (`txRd`,
`txRange`, `txWr` at the caller's view family `R` and scope `S`; the lock calls' triples `retOk`,
`callOk`, `rdSect`, `wrSect`; `applyHook`; the names-only wrappers' `alarmBkt`, `memberBkts`), not
over the backend's predicates. This module, which imports both (the schema never imports the
backend, the backend's API never imports the schema), gives the laws that produce those contracts
for etcd's backend (4a), at two view families defined here. Only the server's proofs (2d, 2e) and
the callers that realize their slots over the backend (3c's lessor, 3d's auth store) import it, as
`MvccStorage.lean` for mvcc.

## The view families (transparent)

* `scopeFp sc`: the cells of a schema scope (a bucket's existence if `sc` may create it, the keys it
  owns; no buffer flag). A caller's part (`beCur γ G C`, `beVis γ G W`) must contain it.
* `btView γ q F G sc X V` (**the batch transaction, its lock held**): a session `beSess γ q F S` with
  the session's whole liveness `beLive γ (btLoc γ) 1` (lent to a range for its bytes), the
  caller's part `beCur γ G C`, the view `V` matching `C` on the scope (`viewOk`: an existing
  bucket's owned keys are `C`'s; an absent bucket the scope may create is absent in `C`, with no owned
  key), the existence of the scope's buckets it may not create for good (`madeIn`: `beMade`, the
  freezer's), and a frame `X` carried through every row (the lock's `Pk` for the `Unlock`, a
  visible-image tracker, ...). A caller begins with any `V` meeting `viewOk` (`imgView C` on the
  buckets it may create, `none` on those not known made).
* `rtView γ G sc X V` (**the shared read transaction, begun**): `beRd γ (rtLoc γ) G W` and its
  liveness `beLive γ (rtLoc γ) 1`, a frame `X W`
  (the caller's knowledge of what it read), the view `V` matching `W` on the scope's keys
  (`viewOkR`; a read of an absent bucket is empty, so existence is not tracked). Begun by
  `RLock` (`rtSect`) or, under the batch lock without `RLock`, by `Backend.beSess_rd` (the
  consistent index read from the post-lock hook, `cindex.go:107`): both give `beRd`.

## The laws, row by row (each against the 4a triple it rests on)

* `bucketAt_ok` (4a's request "from 4a, round 1" (1)): `Schema.bucketAt b bv` gives
  `Backend.bucketOk bv (schemaBi b)`, by `bucket.ID`/`Name`/`IsSafeRangeBucket`'s specs (value
  receivers; `Name()` returns the field's slice, read-only for good in `bucketIs`). `bktsAre_intro`:
  with `New`'s declared set `MvccStorage.schemaBkts` (`beBkt`), every schema bucket value is a
  bucket of the backend (`bkt`), the premise every row needs.
* `safeRegOk_init` (4a's request (2)): the schema's `init` (`bucket.go:62-68`) registers exactly
  the safe-range buckets of `AllBuckets` (`key`), and no other code calls
  `RegisterSafeRangeBucket`: the registry names only safe-range buckets. Rests on the registry
  variable `backend.safeRangeBucketNames` (a `sync.Map`; 4a's `safeRegOk` has no realization over it
  yet, so this law is stated for whatever 4a gives it; 4a should index it by the declared set,
  `safeRegOk Bs`, the law then at `schemaBkts`).
* `btRd` (`txRd`, `txRange` of `btIface γ` at `btView`):
  - single-key `UnsafeRange(b, k, nil, limit)`: `batchTxBuffered.UnsafeRange.spec` (`beSess`, `bkt`,
    `slice.nil ↦*{de} []`); its `btRange` with an empty end is `single (S.cur.ents b) k`, and
    `S.cur` agrees with `C` on the key cell (`beSess_cur`, the key in `scopeFp ⊆ G`), so it is
    `rangeOf m k [] limit` (`viewOk`). The range takes the liveness `beLive γ (btLoc γ) 1` (the
    session is kept); its result `rangeRes kl vl l (beLive …)` is `rangeK`'s (outer slices owned,
    `lentIn`s, the wand giving the liveness back), hence `btView … V` again.
  - interval `UnsafeRange` of a whole bucket (`txRange`): the same triple; `btRange` with `e ≠ []`
    is `sortedEnts … ` cut at a positive limit, which is `rangeOf` (the same three clauses) on the
    whole bucket (every key cell in `G`).
  - `UnsafeForEach` of a whole bucket: `batchTxBuffered.UnsafeForEach.spec` (integration Y: the
    visitor's own error, the bytes kept until given back) with `visitOk vis P E`, `P done := I
    (done.map toLentKV)`, `E done err := J (done.map toLentKV) err` (the two `LentKV`/`Lent` records
    field for field), the liveness `beLive γ (btLoc γ) 1` of the view, given back by the post's
    `lentAll l -∗ beLive …` for the row's `lentKVs l -∗ R V`; `btOrder` gives `entsAny` (sorted keys
    are distinct).
* `btWr` (`txWr` of `btIface γ` at `btView`; the scope must leave `key` alone, `scopeNoKey`, and be
  writable in the session, `writable γ F (scopeFp sc)`):
  - `UnsafePut`: `batchTxBuffered.UnsafePut.spec`: `beCur γ G C` with the key cell in `G`,
    `writable γ F (Fp.key …)` (from the scope's by `beNoVis_mono` or inclusion), the entry bound
    from `putFits` (`k.length + v.length ≤ bboltEntryMax`), `Sess.fresh` only for a safe-range
    bucket (only `key`: excluded). `viewOk` moves with `C.put` (the bucket's names are distinct).
  - `UnsafeDelete`: `batchTxBuffered.UnsafeDelete.spec`: a non-safe-range bucket needs no
    `beDelHeld` (`key` excluded: the schema never deletes from it).
  - `UnsafeCreateBucket`: `batchTxBuffered.UnsafeCreateBucket.spec`'s `some (G, C)` case (the
    existence cell is the scope's, `S.canCreate`); `viewOk`'s absent case (no owned entry) makes the
    created bucket empty, `View.create`.
  - A lent session (`lessor.Revoke`'s `UnsafeDeleteLease` under mvcc's write transaction,
    `ReqLeaseDeleteUnderTxn`): `btView γ q' F G sc X` with mvcc's session (`Mvcc.kbHeld` is
    `beSess γ q' mvccFp S`, `keyBackend_intro`) and the lease part untracked (`beNoVis`, so
    `writable`).
* `rtRd` (`txRd` of `rtIface γ` at `rtView`): `readTx.UnsafeRange.spec` with `covers G b k []`
  (the key in `G`), `es = slice.nil`, `e = []` (no hook premise); `rdRange` with an empty end is
  `single`. `readTx.UnsafeForEach.spec` (the whole bucket in `G`; the view's `beLive γ (rtLoc γ)
  1`): `rdOrder` gives `entsAny` (its keys `Nodup`); the visitor's error and the lent bytes as
  `btRd`'s. **No `txRange` for read transactions**: `rdRange` of a
  safe-range bucket hides the split between bbolt's part and the buffer's (`A.take m ++ B.take n`),
  which is `rangeOf` only when the bucket is clean, and of any other bucket reads at most one
  entry; the schema never ranges a read transaction (`unsafeGetAllRoles` is called on a batch
  transaction only: `nonissues/etcd-auth-readtx-getallroles-panics.md`).
* `rtSect` (`rdSect` of the shared read transaction): `readTx.RLock.spec` with the caller's atomic
  read `AU … COMM X W ∗ ⌜ok (rdView sc W)⌝` and a reader slot; `readTx.RUnlock.spec` gives the slot
  back. `btSectOut` (`wrSect` of `LockOutsideApply`, `CreateMetaBucket`): `LockOutsideApply.spec`
  (`beOpen`, giving `Pk` and an empty session, widened to `F`), then `Unlock.spec`, whose two
  updates the section fires on the caller's tracker `beVis γ F W` (carried in the frame).
* (verify-round, A10-provability B1: the `Lock*` triples give the session's turn `beTurn γ`, which
  `Unlock`'s second update takes back; `btSectOut` carries it in the frame.)
* `beRet`, `btLockIn`, `btLockOut`, `btUnlock`, `beForceCommit`, `rtLock`, `rtUnlock`: the backend
  triples as the schema's `retOk`/`callOk` (`authBackend.ReadTx`/`BatchTx`, `authBatchTx.Lock`/
  `Unlock`, `authReadTx.RLock`/`RUnlock`, both `ForceCommit`s).
* `applyHook_intro`: `LockInsideApply.spec`'s premises (an open share, a hook share, `hookRun γ q
  Pk f Pre Q'`) and the caller's `Q' ={⊤}=∗ Pk ∗ Q` (the wrapper's `Unlock` needs `Pk`) give
  `Schema.applyHook (beIface b) Pre (Q ∗ beOpen γ q ∗ beHook γ dq f)`: the two shares come back in
  the wrapper's post.
* `confStateSave_hook` (second pass, server-core's request for server-boot): the analogue of
  cindex's `ciCells`/`txStoredCI_sess` for the configuration the apply thread saves under the same
  pre-commit hook. `confStateCells`: `meta`'s `confState` key (4a cell). The save
  (`MustUnsafeSaveConfStateToBackend` at the batch transaction) in a hook session `beSess γ q F S`
  (any footprint: after cindex's write it is `ciCells`) with the cell's batch part writes only that
  cell: the session comes back at `Fp.union F confStateCells` with `hookWrites confStateCells S S'` (what 4a's `hookOk` asks of a hook), so the
  server's hook footprint is `Fp.union Cindex.ciCells confStateCells`. Rests on the schema's triple
  over `txWr` at a hook view (as `btWr`, the session published at `confStateCells` by
  `beSess_widen`, one `UnsafePut` of the key: `hookWrites` holds, a put of a cell of `Fh` with the
  base kept); `meta` exists for good (`beMade`).
* `alarmBkt_intro`/`_elim`, `memberBkts_intro`/`_elim`: the names-only wrappers' resources from the
  opener's part of their buckets (batch and visible images, equal; `Schema.alarmsAt`/`memberBktsAt`
  of the image), a reader slot, an open share; and back for the backend's close (whose `beVis`
  must cover every cell). The wrappers' bodies then follow 4a's triples: `CreateAlarmBucket`,
  `MustCreateBackendBuckets` (`LockOutsideApply` on the realization's open share, creates, `Unlock`
  publishing the part); `MustPutAlarm`, `MustDeleteAlarm`, `MustSaveMemberToBackend`, ... (`applyHook`'s
  `LockInsideApply`, a put or delete, `Unlock`); `GetAllAlarms`, `MustReadMembersFromBackend` (the
  realization's slot, `RLock`, `UnsafeForEach`, `RUnlock`).

## Needed of 4a (`backend/Api.lean` and its triples; not this module's to change)

1. **Met (integration Y).** **`UnsafeForEach` returns the visitor's error and lends the bytes until the transaction resource
   is given back** (`batchTxBuffered`, `readTx`, `concurrentReadTx`, `baseReadTx`): `visitOk vis P
   E` whose visitor keeps `ks ↦*{dq} k`, `vs ↦*{dq} v` (no return in its post: `unsafeGetAllUsers`
   appends the value slices and unmarshals after the loop), its error case giving `E done err`, and
   the post `(err = nil ∗ P l ∨ err ≠ nil ∗ E l' err)` with the session/`beRd` back only through a
   wand taking the lent bytes (`Schema.lentKVs`), as `rangeRes` lends against `beLive`. True of the
   code: bbolt's `ForEach` and `bucketBuffer.ForEach` return the visitor's first error (`getDups`
   never fails), and the bytes stay valid while the transaction is held (no write between).
   Without it the rows `btRd`/`rtRd` of `UnsafeForEach` are unprovable.
2. **Bucket existence and bbolt's key errors in the batch rows**: `batchTx.unsafePut`,
   `UnsafeRange` are `lg.Fatal` on a missing bucket, `Put` on an empty or oversized key; 4a's
   `UnsafePut`/`UnsafeSeqPut`/`UnsafeRange`/`UnsafeForEach` triples take no `S.cur.made` premise
   (and `UnsafePut` no key bound). The schema's rows give both (`V b = some m`, `viewOk`/`madeIn`
   give `S.cur.made` by `beSess_cur`/`beMade_cur`; `putFits`), so adding them keeps these laws.
3. **`isBackend` determines its names** (`isBackend γ b p Pk ∗ isBackend γ' b p' Pk' ⊢ ⌜γ = γ' ∧ p =
   p'⌝`): `alarmBkt`, `memberBkts`, `applyHook` hide their `γ`; a wrapper combining two of them, and
   `_elim` feeding the closer's `Close`, must identify them.
4. **The heap binder in every predicate's signature**: `Api.lean`'s opaque predicates (`isBackend`,
   `beCur`, `beSess`, `beFile`, ...) have no `[HeapGS …]` (an opaque body drops unused section
   variables: `#check @isBackend` is `{GF} → BeNames → Loc → GoString → IProp GF → IProp GF`), so
   none can be realized over the heap or bbolt. See `Durable.lean`'s header.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.MvccStorage
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api
public import GeneratedProof.go_etcd_io.raft.v3.raftpb

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

/-! ## The schema's scopes and views over the backend's images -/

section model
variable [GooseExts]

/-- **A schema bucket's identity** as the backend sees it. -/
def schemaBi (b : Schema.Bkt) : BktInfo := ⟨b.name, b.id, b.safe⟩

/-- **The cells of a schema scope**: a bucket's existence if the scope may create it, the keys it
owns. -/
def scopeFp (sc : Schema.Scope) : Fp := fun c =>
  match c with
  | .bkt n => ∃ b : Schema.Bkt, b.name = n ∧ sc.canCreate b
  | .key n k => ∃ b : Schema.Bkt, b.name = n ∧ sc.has b k
  | .buf _ => False

/-- The scope leaves `key` (mvcc's, a safe-range bucket) alone. -/
def scopeNoKey (sc : Schema.Scope) : Prop := sc.keys .key = some [] ∧ sc.create .key = false

/-- **The schema's view of an image** (each bucket's entries if it exists). -/
def imgView (I : Image) : Schema.View := fun b => if I.made b.name then some (I.ents b.name) else none

/-- **`V` is the batch image `C` on the scope**: an existing bucket's owned keys are `C`'s (and it
exists in `C` if the scope may create it); an absent bucket the scope may create is absent in `C`,
with none of the scope's keys. -/
def viewOk (sc : Schema.Scope) (C : Image) (V : Schema.View) : Prop :=
  ∀ b : Schema.Bkt, match V b with
  | some m => (sc.canCreate b → C.made b.name = true) ∧ ∀ k, sc.has b k → m k = C.ents b.name k
  | none => sc.canCreate b → C.made b.name = false ∧ ∀ k, sc.has b k → C.ents b.name k = none

open Classical in
/-- **A read transaction's view on the scope** (a read of an absent bucket is empty). -/
def rdView (sc : Schema.Scope) (W : Image) : Schema.View :=
  fun b => if sc.keys b = some [] then none else some (W.ents b.name)

/-- **`V` is the image `W` on the scope's keys.** -/
def viewOkR (sc : Schema.Scope) (W : Image) (V : Schema.View) : Prop :=
  ∀ (b : Schema.Bkt) (m : Schema.BData) (k : GoString), V b = some m → sc.has b k →
    m k = W.ents b.name k

/-- **`meta`'s `confState` key** (the cell `MustUnsafeSaveConfStateToBackend` writes). -/
def confStateCells : Fp := Fp.key (Schema.Bkt.name .metaB) Schema.confStateKey

/-- The `Alarm` bucket's cells. -/
def alarmFp : Fp := Fp.bucket (Schema.Bkt.name .alarm)

/-- The membership buckets' cells (`Members`, `MembersRemoved`, `Cluster`). -/
def memberFp : Fp :=
  Fp.union (Fp.bucket (Schema.Bkt.name .members))
    (Fp.union (Fp.bucket (Schema.Bkt.name .membersRemoved)) (Fp.bucket (Schema.Bkt.name .cluster)))

end model

/-! ## The view families -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **Every schema bucket value is a bucket of the backend `γ`** (persistent). -/
def bktsAre (γ : BeNames) : IProp GF :=
  iprop(□ ∀ (b : Schema.Bkt) (bv : GoInterface), Schema.bucketAt b bv -∗ bkt γ bv (schemaBi b))

/-- **The scope's buckets it may not create exist for good** where the view says they exist. -/
def madeIn (γ : BeNames) (sc : Schema.Scope) (V : Schema.View) : IProp GF :=
  iprop(□ ∀ (b : Schema.Bkt) (m : Schema.BData), ⌜V b = some m ∧ sc.create b = false⌝ -∗
    beMade γ b.name)

/-- **The batch transaction's view family** (its lock held; see the header). -/
def btView (γ : BeNames) (q : Qp) (F G : Fp) (sc : Schema.Scope) (X : IProp GF)
    (V : Schema.View) : IProp GF :=
  iprop(∃ (S : Sess) (C : Image), beSess γ q F S ∗ beLive γ (btLoc γ) 1 ∗ beCur γ G C ∗
    ⌜viewOk sc C V⌝ ∗ madeIn γ sc V ∗ X)

/-- **The shared read transaction's view family** (begun; see the header). -/
def rtView (γ : BeNames) (G : Fp) (sc : Schema.Scope) (X : Image → IProp GF)
    (V : Schema.View) : IProp GF :=
  iprop(∃ W : Image, beRd γ (rtLoc γ) G W ∗ beLive γ (rtLoc γ) 1 ∗ X W ∗ ⌜viewOkR sc W V⌝)

end vocab

/-! ## Laws (obligations of the schema's and the backend's implementations) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A schema bucket value has its identity** (4a's request; by `bucket.ID`, `Name`,
`IsSafeRangeBucket`'s specs). -/
def bucketAt_ok.spec : Prop := ∀ (b : Schema.Bkt) (bv : GoInterface),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    Schema.bucketAt b bv ⊢ bucketOk bv (schemaBi b)

/-- **The schema's buckets are the backend's** when `New` declared them (`schemaBkts`). -/
def bktsAre_intro.spec : Prop := ∀ γ : BeNames,
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    (□ ∀ bi, ⌜schemaBkts bi⌝ -∗ beBkt γ bi) ⊢ bktsAre γ

/-- **The safe-range registry names only safe-range buckets** after the schema's initialization
(4a's request; rests on the registry variable, see the header). -/
def safeRegOk_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢ safeRegOk

/-- **Reading the batch transaction** (its lock held): `txRd` and `txRange` at `btView`. The
`UnsafeForEach` row rests on 4a's change (1), made at integration Y. -/
def btRd.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F G : Fp) (sc : Schema.Scope) (X : IProp GF),
  ⌜∀ c, scopeFp sc c → G c⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bktsAre γ ⊢
  Schema.txRd (btIface γ) sc (btView γ q F G sc X) ∗
    Schema.txRange (btIface γ) sc (btView γ q F G sc X)

/-- **Writing through the batch transaction** (its lock held): `txWr` at `btView`, for a scope
leaving `key` alone and writable in the session. -/
def btWr.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F G : Fp) (sc : Schema.Scope) (X : IProp GF),
  ⌜(∀ c, scopeFp sc c → G c) ∧ scopeNoKey sc⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bktsAre γ ∗
    writable γ F (scopeFp sc) ⊢
  Schema.txWr (btIface γ) sc (btView γ q F G sc X)

/-- **Reading the shared read transaction** (begun by `RLock`, or by `beSess_rd` under the batch
lock): `txRd` at `rtView`. No `txRange` (see the header). The `UnsafeForEach` row rests on 4a's
change (1), made at integration Y. -/
def rtRd.spec : Prop :=
  ∀ (γ : BeNames) (G : Fp) (sc : Schema.Scope) (X : Image → IProp GF),
  ⌜∀ c, scopeFp sc c → G c⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bktsAre γ ⊢
  Schema.txRd (rtIface γ) sc (rtView γ G sc X)

/-- **A read section of the shared read transaction**: `RLock` from a reader slot and the caller's
atomic read of `G`'s visible image (whose commit gives `X W` and `ok` of the view read), `RUnlock`
giving the slot and `X` back. -/
def rtSect.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (G : Fp) (sc : Schema.Scope)
    (X : Image → IProp GF) (ok : Schema.View → Prop),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ⊢
  Schema.rdSect (rtIface γ)
    iprop(beRdToks γ 1 ∗
      AU <{ ∃∃ (W : Image), beVis γ G W }> @ ⊤, ∅
        <{ beVis γ G W, COMM X W ∗ ⌜ok (rdView sc W)⌝ }>)
    (rtView γ G sc X) ok
    (fun V => iprop(beRdToks γ 1 ∗ ∃ W : Image, X W ∗ ⌜viewOkR sc W V⌝))

/-- **A write section outside apply** (`CreateMetaBucket`'s `wrSect`): `LockOutsideApply` from an
open share, the caller's part at `C0` and its tracker of the published cells `F ⊆ G` (`beVis_none`
for none) gives `btView` at the caller's `V0` (with the lock's `Pk` and the tracker in the frame);
`Unlock` fires the tracker's two updates and gives the share, the part and the tracker back at the
session's final image. -/
def btSectOut.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (F G : Fp)
    (sc : Schema.Scope) (C0 W0 : Image) (V0 : Schema.View) (ok : Schema.View → Prop)
    (X : IProp GF),
  ⌜(∀ c, F c → G c) ∧ viewOk sc C0 V0 ∧ ok V0⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ⊢
  Schema.wrSect (btIface γ) go!"LockOutsideApply"
    iprop(beOpen γ q ∗ beCur γ G C0 ∗ madeIn γ sc V0 ∗ beVis γ F W0 ∗ X)
    (btView γ q F G sc iprop(Pk ∗ beTurn γ ∗ (∃ W : Image, beVis γ F W) ∗ X)) ok
    (fun V => iprop(beOpen γ q ∗ X ∗ ∃ (C W : Image), beCur γ G C ∗ beVis γ F W ∗
      ⌜viewOk sc C V ∧ Image.agree F C W⌝))

/-- **`BatchTx()` and `ReadTx()` return the fixed transactions** (`retOk`). -/
def beRet.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ⊢
  Schema.retOk (beIface b) go!"BatchTx" (btIface γ) ∗ Schema.retOk (beIface b) go!"ReadTx" (rtIface γ)

/-- **`LockInsideApply()`** as a `callOk` (`batchTxBuffered.LockInsideApply.spec`). -/
def btLockIn.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (dq : DFrac) (f : GoFunc)
    (Pre Q : IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ⊢
  Schema.callOk (btIface γ) go!"LockInsideApply"
    iprop(beOpen γ q ∗ beHook γ dq f ∗ Pre ∗ hookRun γ q Pk f Pre Q)
    iprop(∃ I : Image, beSess γ q Fp.none (Sess.init I) ∗ beTurn γ ∗ beLive γ (btLoc γ) 1 ∗
      beHook γ dq f ∗ Q)

/-- **`LockOutsideApply()`** as a `callOk`. -/
def btLockOut.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ⊢
  Schema.callOk (btIface γ) go!"LockOutsideApply" (beOpen γ q)
    iprop(∃ I : Image, beSess γ q Fp.none (Sess.init I) ∗ beTurn γ ∗ beLive γ (btLoc γ) 1 ∗ Pk)

/-- **`Unlock()`** as a `callOk` (`batchTxBuffered.Unlock.spec`: the two visible-image updates). -/
def btUnlock.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (F : Fp) (S : Sess)
    (Ψ1 Ψ2 : IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ⊢
  Schema.callOk (btIface γ) go!"Unlock"
    iprop(beSess γ q F S ∗ beLive γ (btLoc γ) 1 ∗ Pk ∗
      (AU <{ ∃∃ (V : Image), beVis γ F V }> @ ⊤, ∅ <{ beVis γ F S.mid, COMM Ψ1 }>) ∗
      (Ψ1 -∗ AU <{ ∃∃ (V : Image), beVis γ F V ∗ beTurn γ }> @ ⊤, ∅ <{ beVis γ F S.fin, COMM Ψ2 }>))
    iprop(beOpen γ q ∗ Ψ2)

/-- **`ForceCommit()`** of the backend as a `callOk` (`backend.ForceCommit.spec`). -/
def beForceCommit.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (X Y : IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ⊢
  Schema.callOk (beIface b) go!"ForceCommit" iprop(beOpen γ q ∗ X ∗ beReq γ Pk X Y)
    iprop(beOpen γ q ∗ Y)

/-- **The shared read transaction's `RLock()`** as a `callOk` (`readTx.RLock.spec`). -/
def rtLock.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (F : Fp) (Ψ : Image → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ⊢
  Schema.callOk (rtIface γ) go!"RLock"
    iprop(beRdToks γ 1 ∗ AU <{ ∃∃ (V : Image), beVis γ F V }> @ ⊤, ∅ <{ beVis γ F V, COMM Ψ V }>)
    iprop(∃ V : Image, beRd γ (rtLoc γ) F V ∗ beLive γ (rtLoc γ) 1 ∗ Ψ V)

/-- **The shared read transaction's `RUnlock()`** as a `callOk` (`readTx.RUnlock.spec`). -/
def rtUnlock.spec : Prop :=
  ∀ (γ : BeNames) (F : Fp) (V : Image),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ⊢
  Schema.callOk (rtIface γ) go!"RUnlock" iprop(beRd γ (rtLoc γ) F V ∗ beLive γ (rtLoc γ) 1)
    (beRdToks γ 1)

/-- **`applyHook`'s introduction** (replacing 4b's provisional name; see the header): the
`LockInsideApply` premises and the caller's step giving the lock's `Pk` back from the hook's
post; the open and hook shares come back in the wrappers' post. -/
def applyHook_intro.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (dq : DFrac) (f : GoFunc)
    (Pre Q' Q : IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isBackend γ b p Pk ∗ beOpen γ q ∗ beHook γ dq f ∗ hookRun γ q Pk f Pre Q' ∗
    (Q' ={⊤}=∗ Pk ∗ Q) ⊢
  Schema.applyHook (beIface b) Pre iprop(Q ∗ beOpen γ q ∗ beHook γ dq f)

/-- **The alarm bucket's resource from the opener's part** (2e's `NewAlarmStore` over the opened
backend): its batch and visible images, equal, holding `al` (`alarmsAt`), a reader slot, an open
share. -/
def alarmBkt_intro.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (C V : Image)
    (al : Option (List EtcdModel.Alarm)),
  ⌜Image.agree alarmFp C V ∧ Schema.alarmsAt (imgView C .alarm) al⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    isBackend γ b p Pk ∗ bktsAre γ ∗ beOpen γ q ∗ beRdToks γ 1 ∗
    beCur γ alarmFp C ∗ beVis γ alarmFp V ⊢
  |={⊤}=> Schema.alarmBkt (beIface b) al

/-- **The alarm bucket's resource given back** (for the backend's close or a replaced backend). -/
def alarmBkt_elim.spec : Prop :=
  ∀ (b : Loc) (al : Option (List EtcdModel.Alarm)),
  Schema.alarmBkt (GF := GF) (beIface b) al ⊢
  |={⊤}=> ∃ (γ : BeNames) (p : GoString) (Pk : IProp GF) (q : Qp) (C V : Image),
    isBackend γ b p Pk ∗ beOpen γ q ∗ beRdToks γ 1 ∗ beCur γ alarmFp C ∗ beVis γ alarmFp V ∗
    ⌜Image.agree alarmFp C V ∧ Schema.alarmsAt (imgView C .alarm) al⌝

/-- **The membership buckets' resource from the opener's part** (2e's `RaftCluster.SetBackend`
over the opened backend). -/
def memberBkts_intro.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (C V : Image)
    (cb : Option Schema.ClusterBkts),
  ⌜Image.agree memberFp C V ∧ Schema.memberBktsAt (imgView C) cb⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    isBackend γ b p Pk ∗ bktsAre γ ∗ beOpen γ q ∗ beRdToks γ 1 ∗
    beCur γ memberFp C ∗ beVis γ memberFp V ⊢
  |={⊤}=> Schema.memberBkts (beIface b) cb

/-- **The membership buckets' resource given back.** -/
def memberBkts_elim.spec : Prop :=
  ∀ (b : Loc) (cb : Option Schema.ClusterBkts),
  Schema.memberBkts (GF := GF) (beIface b) cb ⊢
  |={⊤}=> ∃ (γ : BeNames) (p : GoString) (Pk : IProp GF) (q : Qp) (C V : Image),
    isBackend γ b p Pk ∗ beOpen γ q ∗ beRdToks γ 1 ∗ beCur γ memberFp C ∗ beVis γ memberFp V ∗
    ⌜Image.agree memberFp C V ∧ Schema.memberBktsAt (imgView C) cb⌝

/-- **Saving the configuration in a pre-commit hook's session writes only `confStateCells`**
(second pass; see the header): from a session at any footprint `F` (the hook's, nothing published,
or already published at `Cindex.ciCells` by the consistent index's write: the two compose, since
`hookWrites` chains) and the cell's batch part, the save returns the session widened by
`confStateCells`, changed only at that cell as `hookWrites` allows, holding the saved bytes at the
key, and the part at them. **Margin** (re-review N4): the saved bytes `bs` are existential, not
stated to be the JSON encoding of `c` (no verified user reads `confState` back). No liveness: the save is one `UnsafePut`, which needs none (the hook is
lent only the session, `hookOk`). -/
def confStateSave_hook.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) (C : Image) (lg cs : Loc) (dq : DFrac)
    (c : Proto.Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bktsAre γ ∗
      beMade γ (Schema.Bkt.name .metaB) ∗ beSess γ q F S ∗ beCur γ confStateCells C ∗
      Proto.msgAt go_etcd_io.raft.v3.raftpb.ConfState.ty cs dq c ∗
      ⌜Schema.confStateKey.length + 128 + 21 * Proto.encSize c ≤ Bbolt.bboltEntryMax⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeSaveConfStateToBackend))
      (Val #lg)) (Val #(btIface γ))) (Val #cs))
  {{ RET #(); Proto.msgAt go_etcd_io.raft.v3.raftpb.ConfState.ty cs dq c ∗
      ∃ (S' : Sess) (C' : Image) (bs : GoString),
        beSess γ q (Fp.union F confStateCells) S' ∗ beCur γ confStateCells C' ∗
        ⌜hookWrites confStateCells S S' ∧
          S'.cur.ents (Schema.Bkt.name .metaB) Schema.confStateKey = some bs ∧
          C'.ents (Schema.Bkt.name .metaB) Schema.confStateKey = some bs⌝ }}

end laws

end Backend
end EtcdGrove
end Perennial
