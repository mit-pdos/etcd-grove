/-
The backend's buffers in memory (`tx_buffer.go`): a bucket buffer, a map of them, the write and
the read buffer, and what `Range`/`ForEach` return. Lean-first (no Rocq counterpart); see
`Model.lean` and `notes/decisions.md`, "The backend: the buffers".

**A bucket buffer** (`bucketBuffer`: a slice of `kv` slots and the number in use) holds the
entries `es` in its first `es.length` slots. Each slot's key and value slices are read-only
for good (`↦*□`): the buffers share them with the caller (the batch transaction keeps the
slices it is given, bbolt too) and with the readers (`Range` returns them, `CopyUsed` copies
the slots). Every slot, in use or stale, has its slices so (`slotsRO`): `merge` reads the
first slot of an empty source buffer. `bbAt bb dq p es` is the buffer at a fraction, its slice
and slots given (`BBPhys`), so that readers holding a fraction agree on them; `ownBB bb es`
owns a writable one (a free slot, as `add` keeps; its length bounded, so `add`'s growth to
`3/2` of it does not overflow).

**A buckets map** (`txBuffer.buckets`, from a bucket id to a buffer pointer): `bksAt m dq P B`
at a fraction with its buffers' layout `P`; `ownBks m B` writable.

**The buffers.** `ownWB txw W` owns a write buffer (the fields of the `txWriteBuffer` at
`txw`, its buckets and flags), `ownRB txr R` a read buffer; `rbAt txr dq m P R` is a read
buffer at a fraction, for readers.

**Results.** `kvsOut keys vals res`: the two slices `Range` returns, owned, of the entries'
keys and values (read-only); `isBucket b bi`: the `Bucket` interface value `b` whose `ID()`,
`Name()` and `IsSafeRangeBucket()` return `bi`'s; `visitorSpec f es P Q`: a `ForEach` visitor
over the entries `es`, `P i` its state after `i` of them, `Q err` if it fails.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section phys
variable [GooseExts]

/-- A bucket buffer's slice and its slots. -/
structure BBPhys where
  buf : GoSlice
  kvs : List kv

/-- A writable buffer has a free slot, at least two slots (so that growing to `3/2` of its
length gives a free slot again), and is small enough to grow. -/
def bbOk (p : BBPhys) (es : List Ent) : Prop :=
  es.length < p.kvs.length ∧ 2 ≤ p.kvs.length ∧ p.kvs.length ≤ 2 ^ 61

/-- A buckets map's buffers: by bucket id, the buffer's pointer and layout. -/
abbrev BksPhys := GMap w64 (Loc × BBPhys)

end phys

/-- The bucket `b` as `Bucket`'s methods report it. -/
structure BucketInfo where
  id : w64
  name : GoString
  safe : Bool

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- Every slot's key and value slices hold some bytes, read-only. -/
def slotsRO (kvs : List kv) : IProp GF :=
  iprop([∗list] x ∈ kvs, ∃ (b1 b2 : GoString), x.key' ↦*□ b1 ∗ x.val' ↦*□ b2)

/-- The first slots hold the entries, read-only. -/
def entsIn (kvs : List kv) (es : List Ent) : IProp GF :=
  iprop(⌜es.length ≤ kvs.length⌝ ∗ [∗list] x ∈ kvs.zip es, x.1.key' ↦*□ x.2.1 ∗ x.1.val' ↦*□ x.2.2)

/-- The bucket buffer at `bb`, at fraction `dq`, with slice and slots `p`, holding `es`. -/
def bbAt (bb : Loc) (dq : DFrac) (p : BBPhys) (es : List Ent) : IProp GF :=
  iprop(bb ↦{dq} ({ buf' := p.buf, used' := W64 es.length } : bucketBuffer) ∗
    p.buf ↦*{dq} p.kvs ∗ ownSliceCap kv p.buf dq ∗ slotsRO p.kvs ∗ entsIn p.kvs es)

/-- The buckets map `m` at fraction `dq`, its buffers laid out as `P`, holding `B`. -/
def bksAt (m : GoMap) (dq : DFrac) (P : BksPhys) (B : GMap w64 (List Ent)) : IProp GF :=
  iprop(m ↦${dq} P.fmap Prod.fst ∗ [∗map] _id ↦ x;es ∈ P;B, bbAt x.1 dq x.2 es)

/-- A writable buckets map holding `B` (every buffer writable). -/
def ownBks (m : GoMap) (B : GMap w64 (List Ent)) : IProp GF :=
  iprop(∃ P : BksPhys, bksAt m (DFrac.own 1) P B ∗
    ⌜∀ id x es, P.lookup id = some x → B.lookup id = some es → bbOk x.2 es⌝)

/-- The write buffer at `txw` (the fields of a `txWriteBuffer`) holding `W`. -/
def ownWB (txw : Loc) (W : WBuf) : IProp GF :=
  iprop(∃ (m s : GoMap),
    structFieldRef txWriteBuffer go!"txBuffer" txw ↦ ({ buckets' := m } : txBuffer) ∗
    structFieldRef txWriteBuffer go!"bucket2seq" txw ↦ s ∗
    ownBks m W.bks ∗ s ↦$ W.seq)

/-- The read buffer at `txr` at fraction `dq`, its map `m` and buffers `P`, holding `R`. -/
def rbAt (txr : Loc) (dq : DFrac) (m : GoMap) (P : BksPhys) (R : RBuf) : IProp GF :=
  iprop(structFieldRef txReadBuffer go!"txBuffer" txr ↦{dq} ({ buckets' := m } : txBuffer) ∗
    structFieldRef txReadBuffer go!"bufVersion" txr ↦{dq} R.ver ∗ bksAt m dq P R.bks)

/-- `b` is a `Bucket` with id, name and safe-range flag `bi` (persistent). -/
def isBucket (b : GoInterface) (bi : BucketInfo) : IProp GF :=
  iprop(∃ bo : GoInterfaceOk, ⌜b = GoInterface.ok bo⌝ ∗
    □ ({{ True }} (App (Val #(methods bo.ty go!"ID" bo.v)) (Val #()))
      {{ RET #bi.id; True }}) ∗
    □ ({{ True }} (App (Val #(methods bo.ty go!"Name" bo.v)) (Val #()))
      {{ (s : GoSlice), RET #s; s ↦*□ bi.name }}) ∗
    □ ({{ True }} (App (Val #(methods bo.ty go!"IsSafeRangeBucket" bo.v)) (Val #()))
      {{ RET #bi.safe; True }}))

end defs

/-! ## The slots of a buffer -/

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Iris.ProofMode

end slots

end backend
end EtcdGrove
end Perennial
