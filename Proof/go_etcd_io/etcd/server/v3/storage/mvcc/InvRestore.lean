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

end defs

end EtcdGrove
end Perennial
