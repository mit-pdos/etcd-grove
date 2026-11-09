/-
`restoreChunk(lg, kvc, keys, vals, keyToLease)` (`kvstore.go:493`). Internal: `restore`, per chunk
of the `Key` bucket read.

**Proof sketch**: per entry: a fresh `mvccpb.KeyValue`, `proto.Unmarshal` of the value's lent bytes
(`kvDecodes`: no `lg.Fatal`; the content copied, so the value bytes come back), the key-to-lease map
updated (`ktlApply`), the restored form sent (`rkvSend`: the key's lent bytes go with it, joining the
producer's loans, regrouped as the chunk's `lentIn` by `rkvProducer_mono`).

**Changes** from `specs-ref`'s file: the channel's protocol `rkvProducer` (the entries a prefix of
what remains to send), the map `ktlMap`, no reader capability.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `restoreChunk(lg, kvc, keys, vals, mp)` of the entries `ents`, the next ones of `all` after `n`
sent: each sent, the key-to-lease map updated. -/
def restoreChunk.spec : Prop :=
  ∀ (lg kvc mp : Loc) (keys vals : GoSlice) (ps qs : List GoSlice) (dq : DFrac)
    (all ents : List KvEnt) (n : Nat) (L : IProp GF) (M : GoString → Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ Zap.isLogger lg ∗
      keys ↦* ps ∗ vals ↦* qs ∗
      Schema.lentIn dq (ents.map KvEnt.bk) ps ∗ Schema.lentIn dq (ents.map KvEnt.vb) qs ∗
      ⌜(∀ e ∈ ents, kvDecodes e.vb e.kv) ∧ (all.drop n).take ents.length = ents⌝ ∗
      ktlMap mp M ∗ rkvProducer kvc all n L }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.restoreChunk))
      (Val #lg)) (Val #kvc)) (Val #keys)) (Val #vals)) (Val #mp))
  {{ RET #(); keys ↦* ps ∗ vals ↦* qs ∗ Schema.lentIn dq (ents.map KvEnt.vb) qs ∗
      ktlMap mp (ktlApply M ents) ∗
      rkvProducer kvc all (n + ents.length) iprop(L ∗ Schema.lentIn dq (ents.map KvEnt.bk) ps) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
