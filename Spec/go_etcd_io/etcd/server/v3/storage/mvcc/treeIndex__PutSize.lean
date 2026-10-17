/-
`treeIndex.PutSize` (`index.go`, etcd-io/etcd#22096). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
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

/-- `ti.PutSize(key, rev, size)` (etcd-io/etcd#22096) by the writer, for the next change of the
pending revision (a put of `key`, with any value `v` and lease, keeping the log well formed),
`size` the put's live size `len(key) + len(v)`: the key's index gets the revision (a fresh index
if it has none), and the writer's log has the change, as for `Put`; and it records `size` as the
key's live size and returns the key's live size before the put (`LivePayload.lean`: `len(key) +
len(value)` of its live version, `0` if the key was absent or deleted). The key's bytes are
read-only for good (the index keeps them). -/
abbrev mvcc.treeIndex.PutSize.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (key : GoSlice)
    (k : GoString) (rev : Revision) (v : GoString) (l : w64) (size : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxWriter γ ilog pend ∗ key ↦*□ k ∗
      ⌜mvcc.revOf rev = ⟨W64 ilog.length, W64 pend.length⟩ ∧ 1 ≤ ilog.length ∧
        pend.length + 1 < 2 ^ 63 ∧ mvcc.LogWf' (ilog ++ [pend ++ [.put k v l]]) ∧
        size = W64 ((k.length + v.length : Nat) : Int)⌝ }}
    (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"PutSize")) (Val #key))
      (Val #rev)) (Val #size))
  {{ RET #(mvcc.liveW (ilog ++ [pend]) k); mvcc.idxWriter γ ilog (pend ++ [.put k v l]) }}

end spec

end EtcdGrove
end Perennial

