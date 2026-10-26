/-
`restoreChunk` (`kvstore.go`; translated 2026-10-23, the restore plan's R0). Lean-first (no Rocq
counterpart); see `InvRestore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRestore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `restoreChunk(lg, kvc, keys, vals, keyToLease)` of the bucket entries `ents` (`keys`/`vals`
read-only slices of their keys and values, in order, readable through `Rd` under the token `Tok`,
kept; each value the encoding of a key-value, so `proto.Unmarshal` returns `nil` and `lg.Fatal` is
unreachable), none with a lease (`keyToLease`, empty, stays so: every branch deletes the key), on
`kvc` the producer side of a single-producer channel (`isSpsc` with the protocol `P`): sends one
`revKeyValue` per entry, in order, the `j`-th (`sent.length + j` on the channel) the entry's
restored form (`rkvIs`) with the entry's resource `Q j e`, which the caller's `□` turns into
`P`. -/
abbrev mvcc.restoreChunk.spec : Prop :=
  ∀ (lg kvc mp : Loc) (keys vals : GoSlice) (ents : List mvcc.KvEnt)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (γ : SpscNames)
    (P : Int → revKeyValue → IProp GF) (R : List revKeyValue → IProp GF)
    (sent : List revKeyValue) (Q : Nat → mvcc.KvEnt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.pairVals Rd keys vals (ents.map mvcc.KvEnt.pair) ∗ mvcc.rdCap Rd Tok ∗ Tok ∗
      ⌜∀ e ∈ ents, e.kv.lease = W64 0⌝ ∗ mp ↦$ (∅ : GMap GoString w64) ∗
      isSpsc γ kvc P R ∗ spscProducer γ sent ∗
      ([∗list] j ↦ e ∈ ents, Q j e) ∗
      □ (∀ (j : Nat) (e : mvcc.KvEnt) (rkv : revKeyValue), ⌜ents[j]? = some e⌝ -∗ Q j e -∗
        mvcc.rkvIs Rd rkv e -∗ P (sent.length + j) rkv) }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.restoreChunk))
      (Val #lg)) (Val #kvc)) (Val #keys)) (Val #vals)) (Val #mp))
  {{ RET #(); Tok ∗ mp ↦$ (∅ : GMap GoString w64) ∗
      ∃ new : List revKeyValue, ⌜new.length = ents.length⌝ ∗ spscProducer γ (sent ++ new) }}

end spec

end EtcdGrove
end Perennial
