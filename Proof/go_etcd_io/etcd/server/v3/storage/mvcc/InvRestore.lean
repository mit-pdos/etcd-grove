/-
**The store's restore from its backend** (the restore plan, `notes/restore-plan.md`, R1-R3): what
`restoreChunk` sends `restoreIntoIndex`'s goroutine for a bucket entry. Lean-first (no Rocq
counterpart).

`rkvIs Rd rkv e`: the `revKeyValue` `rkv` is the restored form of the bucket entry `e`
(`KvEnt`: its revision, tombstone mark and key-value): its `key` is the entry's bucket key, read
through `Rd` (`□ Rd`, as the backend's read returns it: `rdB`, the read buffer's bytes or bbolt's
open read transaction's, `UnsafeRange`'s `kvsOutRd`), its `kstr` the key-value's key, and its `kv`
a `*mvccpb.KeyValue` holding the key-value's fields as `proto.Unmarshal` decodes them (key and
value as read-only slices, the message's internal fields as it left them), owned.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.IdxPriv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A `revKeyValue` (a key slice, a message pointer, a key string) is countable: the values a
single-producer channel's history records (`spscProducer`). -/
instance mvcc.revKeyValue_countable : Pos.Countable revKeyValue :=
  .ofInjective (fun r => Pos.Countable.encode (r.key', r.kv', r.kstr'))
    (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- The `mvccpb.KeyValue` message `proto.Unmarshal` leaves for the key-value `kv`: its fields, the
key and value at the slices `ks`, `vs`, the message's internal fields `st`, `uf`, `sc`. -/
def mvcc.kvMsgOf (st : internal.impl.MessageState) (ks vs uf : GoSlice) (sc : w32) (kv : EtcdKv) :
    mvccpb.KeyValue :=
  { state' := st, Key' := ks, CreateRevision' := kv.createRev, ModRevision' := kv.modRev,
    Version' := kv.version, Value' := vs, Lease' := kv.lease, unknownFields' := uf,
    sizeCache' := sc }

/-- **`rkv` is the restored form of the bucket entry `e`** (see the file header). -/
def mvcc.rkvIs (Rd : GoSlice → GoString → IProp GF) (rkv : revKeyValue) (e : mvcc.KvEnt) :
    IProp GF :=
  iprop(□ Rd rkv.key' (mvcc.revBytes e.rev e.tomb) ∗ ⌜rkv.kstr' = e.kv.key⌝ ∗
    ∃ (ks vs uf : GoSlice) (st : internal.impl.MessageState) (sc : w32),
      rkv.kv' ↦ mvcc.kvMsgOf st ks vs uf sc e.kv ∗ ks ↦*□ e.kv.key ∗ vs ↦*□ e.kv.value)

/-- **What the rebuild does with one bucket entry** (`restoreIntoIndex`'s loop body, on the
model of the index): a key the index has gets the entry's revision (`put`, or `tombstone`, which
changes nothing when the key's last generation is already empty: the code logs the error and
goes on); a key it does not have gets a new key index (`restore` with the key-value's create
revision and version, or `restoreTombstone`). -/
def mvcc.idxRestoreEnt (idx : mvcc.IndexM) (e : mvcc.KvEnt) : mvcc.IndexM :=
  match mvcc.idxGet idx e.kv.key with
  | some ki =>
    if e.tomb then
      (if mvcc.kiLastEmpty ki then idx
       else btInsert mvcc.idxLess (e.kv.key, mvcc.kiTombstone ki e.rev) idx)
    else btInsert mvcc.idxLess (e.kv.key, mvcc.kiPut ki e.rev) idx
  | none =>
    btInsert mvcc.idxLess (e.kv.key,
      if e.tomb then mvcc.kiRestoreTombstone e.rev
      else mvcc.kiRestore e.kv.createRev e.rev e.kv.version) idx

/-- The index the rebuild makes of the bucket entries `ents`, in order. -/
def mvcc.idxRestore (ents : List mvcc.KvEnt) : mvcc.IndexM := ents.foldl mvcc.idxRestoreEnt []

/-- The bucket entries the rebuild can take without panicking: in increasing revision order (as
`UnsafeRange` returns the `Key` bucket), their revisions positive (`currentRev` starts at `1`:
`verify.Verify`'s check) with a non-negative sub-revision. -/
def mvcc.RestoreEntsOk (ents : List mvcc.KvEnt) : Prop :=
  ents.Pairwise (fun a b => mvcc.Rev.lt a.rev b.rev) ∧
    ∀ e ∈ ents, 1 ≤ sint.Z e.rev.main ∧ 0 ≤ sint.Z e.rev.sub

/-- The revision `restoreIntoIndex`'s goroutine answers after the entries `ents`: the last one's
main revision, `1` if there is none. -/
def mvcc.restoreLastRev (ents : List mvcc.KvEnt) : w64 :=
  match ents.getLast? with
  | some e => e.rev.main
  | none => W64 1

end defs

section protos
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`rkvc`'s protocol**: its `i`-th value is the restored form of the `i`-th bucket entry. -/
def mvcc.rkvProt (Rd : GoSlice → GoString → IProp GF) (ents : List mvcc.KvEnt) (i : Int)
    (rkv : revKeyValue) : IProp GF :=
  iprop(∃ e, ⌜ents[i.toNat]? = some e ∧ 0 ≤ i⌝ ∗ mvcc.rkvIs Rd rkv e)

/-- **`revc`'s protocol**: its one value is the last revision, with the rebuilt private index,
the reader's token back and a time receipt per entry (each entry is put into the index by a step
of the goroutine: D22h, `restoreIdxPost`). -/
def mvcc.revProt (ti : Loc) (Tok : IProp GF) (ents : List mvcc.KvEnt) (i : Int) (v : w64) :
    IProp GF :=
  iprop(⌜i = 0 ∧ v = mvcc.restoreLastRev ents⌝ ∗ Tok ∗ ⧗ ents.length ∗
    ∃ L, mvcc.ownIdxPriv ti L ∗ ⌜mvcc.idxOfEntries L = mvcc.idxRestore ents⌝)

end protos

end EtcdGrove
end Perennial
