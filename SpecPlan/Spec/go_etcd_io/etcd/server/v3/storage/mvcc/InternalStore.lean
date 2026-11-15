/-
# mvcc's store internals (batch 3e): the vocabulary of the compaction, restore, hashing and
metadata helpers' specs

Imported by mvcc's own spec files only. Pure models transparent, resources opaque.

## Pure

* `KvEnt`: an entry of the `Key` bucket as `restore` reads it: its key bytes, value bytes and the
  key-value they decode to; `kvDecodes vb m` (opaque: `proto.Unmarshal` of `vb` into a fresh
  `mvccpb.KeyValue` succeeds with content `m`; mvcc's image realization: the bucket's values are
  `proto.Marshal`'s, `SpecPlan/Spec/google_golang_org/protobuf/proto`'s `encodes`); `RestoreEntsOk` (each
  key a well-formed revision, each value decoding, revisions increasing: what an image's bucket
  read in order gives); `idxRestore` (the index `restoreIntoIndex` rebuilds), `lastMain` (the
  revision it reports), `ktlApply` (`restoreChunk`'s key→lease map).
* `metaRev o`: what `UnsafeRead{Finished,Scheduled}Compact` returns of a compaction key's value.

## Resources (opaque)

* `storeWB s γ B Pk` (exclusive): `s.mu` held for writing, the store's storage `B` (batch-lock
  invariant `Pk`), with what `s.mu` protects (the store's fields, its invariant's storage-data
  protocol: the visible data at the image of the committed history).
* `revsAt γ cur c` (exclusive; `s.revMu`'s invariant's): the store's current and compaction
  revisions (`currentRev`, `compactMainRev`); the store's invariant ties them to `mvccState`.
* `schedRight s γ` (exclusive): a share of the store's scheduler (the open token's): `Schedule`
  may be called. `storeStopped s γ` (persistent): the store's current stop channel is closed (what a
  job learns when its context is done, `Schedule.schedCtx`'s `Pay`). `compactCh ch` (exclusive):
  the right to close a compaction's channel.
* `storeRestoring s γ B Pk le` (exclusive): `restore`'s start: `s.mu` held for writing, `s.b = B`,
  a fresh private index, `currentRev = 1`, `compactMainRev = -1`, a fresh scheduler and stop
  channel, `s.le = le`. `storeRestored s γ B Pk h` (exclusive): its end, the store's fields at the
  image of `h` (`currentRev = h.rev`, `compactMainRev` its compaction, the index `h`'s, published).
* `rkvProducer c ents n L`, `revConsumer c kc ti ents` (exclusive): `restoreIntoIndex`'s two channels:
  `n` of the entries' restored forms sent (in order), their key bytes `L` lent to the index
  goroutine (bbolt's, lent against the read transaction's liveness: the goroutine reads them until
  it reports); `rkvClosed c L` once `rkvc` is closed; the index goroutine's result, with `L` back
  (`revRecv`).
* `ktlMap mp M` (exclusive): `restore`'s key→lease map. `keepMap mp dq K` (fractional): a
  `map[Revision]struct{}` holding `K`.
* `hasherAt hp c r keep` (exclusive), `hasherVal h c r keep` (persistent): a `kvHasher` (at `hp`,
  or the value `h`) of compaction revision `c`, revision `r`, keep map `keep`.
* `hashStorageFresh hs s` (exclusive): a new `*hashStorage` over `s`, nothing stored.
* `schemaVars` (persistent): schema's globals mvcc reads (`schema.Key`, `schema.Meta`: their
  values (`Schema.bucketAt`, 4b's `bucketVars_init`); the compaction keys' names: `metaKey`): schema's initialization law (4b's).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Internal
public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.schedule.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.server.v3.storage.schema

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.server.v3.storage.mvcc
open Classical

section pure
variable [GooseExts]

/-- A `Key` bucket entry as `restore` reads it. -/
structure KvEnt where
  bk : GoString
  vb : GoString
  kv : KeyValueM

/-- **`vb` decodes to a `mvccpb.KeyValue` of content `m`** (opaque; see the header). -/
opaque kvDecodes (vb : GoString) (m : KeyValueM) : Prop

/-- The entry's revision and tombstone flag. -/
def KvEnt.rev (e : KvEnt) : Rev := ((revOfBytes e.bk).map Prod.fst).getD Rev.zero

/-- **Entries `restore` can read**: keys well-formed revisions, values decoding, revisions
increasing (as the bucket's byte order gives). -/
def RestoreEntsOk (ents : List KvEnt) : Prop :=
  (∀ e ∈ ents, (revOfBytes e.bk).isSome ∧ kvDecodes e.vb e.kv) ∧
  ents.Pairwise (fun a b => Rev.gt b.rev a.rev = true)

/-- One entry restored into the index (`restoreIntoIndex`'s loop). -/
def idxRestoreStep (M : IndexM) (e : KvEnt) : IndexM :=
  let k := e.kv.key
  let r := e.rev
  match M k with
  | some ki =>
    if isTombBytes e.bk then
      (match kiTombstone ki r with
       | some ki' => fun k' => if k' = k then some ki' else M k'
       | none => M)
    else fun k' => if k' = k then some (kiPut ki r) else M k'
  | none =>
    let ki := if isTombBytes e.bk then kiRestoreTombstone r
      else kiRestore ⟨e.kv.createRevision, W64 0⟩ r e.kv.version
    fun k' => if k' = k then some ki else M k'

/-- The index `restoreIntoIndex` rebuilds from `ents`. -/
def idxRestore (ents : List KvEnt) : IndexM := ents.foldl idxRestoreStep (fun _ => none)

/-- The revision `restoreIntoIndex` reports: the last entry's main, `1` if none. -/
def lastMain (ents : List KvEnt) : w64 := (ents.getLast?.map (fun e => e.rev.main)).getD (W64 1)

/-- `restoreChunk`'s key→lease map after `ents` (a tombstone or no lease removes the key). -/
def ktlApply (M : GoString → Option w64) (ents : List KvEnt) : GoString → Option w64 :=
  ents.foldl (fun M e => fun k =>
    if k = e.kv.key then
      (if isTombBytes e.bk ∨ e.kv.lease = W64 0 then none else some e.kv.lease)
    else M k) M

/-- What `UnsafeRead*Compact` returns of a compaction key's value (`BytesToRev(..).Main`, found). -/
def metaRev (o : Option GoString) : w64 × Bool :=
  match o with
  | some b => (((revOfBytes b).map (fun p => p.1.main)).getD (W64 0), true)
  | none => (W64 0, false)

/-- A compaction key's value parses (`BytesToRev` does not panic). -/
def metaOk (o : Option GoString) : Prop := ∀ b, o = some b → (revOfBytes b).isSome

end pure

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `s.mu` held for writing; the store's storage is `B`, its batch lock's invariant `Pk`. -/
opaque storeWB [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : MvccName) (B : MvccStorage) (Pk : IProp GF) : IProp GF := iprop(True)

/-- The store's current and compaction revisions (`s.revMu`'s). -/
opaque revsAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : MvccName) (cur : Nat) (c : Int) : IProp GF := iprop(True)

/-- A share of the store's scheduler. -/
opaque schedRight [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- The store's current stop channel is closed (persistent). -/
opaque storeStopped [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- The right to close a compaction's channel `ch` (once). -/
opaque compactCh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : GoChan) : IProp GF := iprop(True)

/-- `restore`'s start (see the header). -/
opaque storeRestoring [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : MvccName) (B : MvccStorage) (Pk : IProp GF) (le : GoInterface) :
    IProp GF := iprop(True)

/-- `restore`'s end: the store's fields at the image of `h`. -/
opaque storeRestored [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : MvccName) (B : MvccStorage) (Pk : IProp GF) (h : KVHist) :
    IProp GF := iprop(True)

/-- `n` of `ents`' restored forms sent on `c`, their key bytes `L` lent to the receiver. -/
opaque rkvProducer [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Loc) (ents : List KvEnt) (n : Nat) (L : IProp GF) : IProp GF := iprop(True)

/-- `c` closed after every entry was sent, the key bytes `L` still lent to the receiver. -/
opaque rkvClosed [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Loc) (L : IProp GF) : IProp GF := iprop(True)

/-- The index goroutine's result channel `c` (its one value: the last revision, with the index), the
entries coming on `kc`. -/
opaque revConsumer [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c kc : Loc) (ti : Loc) (ents : List KvEnt) : IProp GF := iprop(True)

/-- `restore`'s key→lease map. -/
opaque ktlMap [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (mp : Loc) (M : GoString → Option w64) : IProp GF := iprop(True)

/-- A `map[Revision]struct{}` holding `K` (fraction `dq`). -/
opaque keepMap [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (mp : GoMap) (dq : DFrac) (K : Rev → Prop) : IProp GF := iprop(True)

/-- A `kvHasher` at `hp` (compaction revision `c`, revision `r`, keep map `keep`). -/
opaque hasherAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (hp : Loc) (c r : w64) (keep : GoMap) : IProp GF := iprop(True)

/-- The `kvHasher` value `h` (persistent). -/
opaque hasherVal [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (h : kvHasher) (c r : w64) (keep : GoMap) : IProp GF := iprop(True)

/-- A new `*hashStorage` over `s`. -/
opaque hashStorageFresh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (hs s : Loc) : IProp GF := iprop(True)

/-- Schema's globals mvcc reads (persistent; schema's initialization, 4b). -/
def schemaVars : IProp GF :=
  iprop((∃ bv, globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ bv ∗ Schema.bucketAt .key bv) ∗
    (∃ bv, globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ bv ∗
      Schema.bucketAt .metaB bv) ∗
    (∃ sl : GoSlice, globalAddr go_etcd_io.etcd.server.v3.storage.schema.ScheduledCompactKeyName ↦□ sl ∗
      sl ↦*□ metaKey .sched) ∗
    (∃ sl : GoSlice, globalAddr go_etcd_io.etcd.server.v3.storage.schema.FinishedCompactKeyName ↦□ sl ∗
      sl ↦*□ metaKey .fin))

/-- A restored entry sent on `rkvc`: the bucket key's bytes (at `dq`: the storage's, lent), a fresh
key-value of the entry's content, its key as a string. -/
def rkvIs (v : revKeyValue) (e : KvEnt) (dq : DFrac) : IProp GF :=
  iprop(v.key' ↦*{dq} e.bk ∗ keyValueOwn v.kv' (DFrac.own 1) e.kv ∗ ⌜v.kstr' = e.kv.key⌝)

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def store_persistent.spec : Prop :=
  (∀ s γ, Persistent (storeStopped (GF := GF) s γ)) ∧
  (∀ h c r keep, Persistent (hasherVal (GF := GF) h c r keep)) ∧
  (∀ mp K, Persistent (keepMap (GF := GF) mp DFrac.discard K))

/-- The storage `s.mu`'s holder names is the client's share's. -/
def storeWB_agree.spec : Prop :=
  ∀ s γ B B' (Pk Pk' : IProp GF) q, storeWB (GF := GF) s γ B Pk ∗ mvccBackend γ q B' Pk' ⊢
    ⌜B = B' ∧ Pk = Pk'⌝

/-- `restore` holds `s.mu` with the store's storage named. -/
def storeRestoring_wb.spec : Prop :=
  ∀ s γ B (Pk : IProp GF) le, storeRestoring (GF := GF) s γ B Pk le ⊢
    storeWB s γ B Pk ∗ (storeWB s γ B Pk -∗ storeRestoring s γ B Pk le)

/-- A hasher value stored at `hp`. -/
def hasherAt_intro.spec : Prop :=
  ∀ (hp : Loc) h c r keep, hp ↦ h ∗ hasherVal (GF := GF) h c r keep ⊢ hasherAt hp c r keep

/-- Sending the next restored form on `rkvc` (its key bytes join the loans). -/
def rkvSend.spec : Prop :=
  ∀ (c : Loc) ents n (L : IProp GF) e (v : revKeyValue) (dq : DFrac) (Φ : val → IProp GF),
    ⌜ents[n]? = some e⌝ -∗ rkvProducer (GF := GF) c ents n L -∗ rkvIs v e dq -∗
    ▷ (rkvProducer c ents (n + 1) iprop(L ∗ v.key' ↦*{dq} e.bk) -∗ Φ #()) -∗
    WP (App (App (Val (chan.send revKeyValue.ty)) (Val #c)) (Val #v)) {{ Φ }}

/-- **One decoding relation** (3f's `kvsToEvents` unmarshals what the image law, `mvccImage_above`,
calls `kvBytes`): an image's encoding of a key-value is what `proto.Unmarshal` decodes to it
(`kvDecodes`, which `restoreChunk` uses). -/
def kvBytes_decodes.spec : Prop := ∀ (m : KeyValueM) (bs : GoString), kvBytes m bs → kvDecodes bs m

/-- The loans the producer holds may be weakened (regrouped: a chunk's keys as one `lentIn`). -/
def rkvProducer_mono.spec : Prop :=
  ∀ (c : Loc) ents n (L L' : IProp GF),
    rkvProducer (GF := GF) c ents n L ∗ (L -∗ L') ⊢ rkvProducer c ents n L'

/-- Closing `rkvc` once every entry was sent (`restore`'s `close(rkvc)`). -/
def rkvClose.spec : Prop :=
  ∀ (c : Loc) ents (L : IProp GF) (Φ : val → IProp GF),
    rkvProducer (GF := GF) c ents ents.length L -∗ ▷ (rkvClosed c L -∗ Φ #()) -∗
    WP (App (App (Val (GoInstruction (FuncResolve go.close
      [(go.GoType.ChannelType go.ChanDir.sendonly revKeyValue.ty)]))) (Val #())) (Val #c)) {{ Φ }}

/-- Receiving the index goroutine's result, once every entry was sent and `rkvc` closed: the index,
and the key bytes lent to the goroutine back. -/
def revRecv.spec : Prop :=
  ∀ (c kc ti : Loc) ents (L : IProp GF) (Φ : val → IProp GF),
    revConsumer (GF := GF) c kc ti ents -∗ rkvClosed kc L -∗
    ▷ (∀ P, ownIdxPriv ti P -∗ ⌜privModel P = idxRestore ents⌝ -∗ L -∗
        Φ (PairV #(lastMain ents) #true)) -∗
    WP (App (Val (chan.receive go.int64)) (Val #c)) {{ Φ }}

/-- A new hash storage, once the store's handle exists. -/
def hashStorageFresh_share.spec : Prop :=
  ∀ hs s γ, isStore (GF := GF) s γ ∗ hashStorageFresh hs s ={⊤}=∗ isHashStorageAt hs s γ

/-- The internal handle under the client's. -/
def isHashStorageAt_api.spec : Prop :=
  ∀ hs s γ, isHashStorageAt (GF := GF) hs s γ ⊢
    isHashStorage (interface.mkOk (go.GoType.PointerType hashStorage.ty) #hs) γ

end laws

end Mvcc
end EtcdGrove
end Perennial
