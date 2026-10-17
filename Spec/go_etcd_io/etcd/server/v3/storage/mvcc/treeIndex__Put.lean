/-
`treeIndex.Put` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `ti.Put(key, rev, valueSize)` by the writer, for the next change of the pending revision (a
put of `key`, with any value and lease, keeping the log well formed), `valueSize` the value's
length: the key's index gets the revision (a fresh index if it has none), and the writer's log
has the change. It returns what the put adds to the live payload (etcd-io/etcd#22475,
`LivePayload.lean`): the key's part after the put (`len(key) + len(value)`) less its part before
(`0` if the key was absent or deleted), mod `2^64`. The key's bytes are read-only for good (the
index keeps them). -/
abbrev mvcc.treeIndex.Put.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (key : GoSlice)
    (k : GoString) (rev : Revision) (v : GoString) (l : w64) (valueSize : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxWriter γ ilog pend ∗ key ↦*□ k ∗
      ⌜mvcc.revOf rev = ⟨W64 ilog.length, W64 pend.length⟩ ∧ 1 ≤ ilog.length ∧
        pend.length + 1 < 2 ^ 63 ∧ mvcc.LogWf' (ilog ++ [pend ++ [.put k v l]]) ∧
        valueSize = W64 v.length⌝ }}
    (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Put")) (Val #key))
      (Val #rev)) (Val #valueSize))
  {{ RET #(mvcc.liveW (ilog ++ [pend ++ [.put k v l]]) k - mvcc.liveW (ilog ++ [pend]) k);
      mvcc.idxWriter γ ilog (pend ++ [.put k v l]) }}

end spec

end EtcdGrove
end Perennial

