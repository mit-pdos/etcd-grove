/-
`treeIndex.Tombstone` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
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

/-- `ti.Tombstone(key, rev)` by the writer, for the next change of the pending revision (a
delete of `key`, which the well-formed log says is present): `nil`, the key's index gets the
tombstone, and the writer's log has the change. It returns what the delete adds to the live
payload (etcd-io/etcd#22475, `LivePayload.lean`): the key's part after the delete (`0`) less its
part before (`len(key) + len(value)` of the deleted key-value), mod `2^64`. -/
abbrev mvcc.treeIndex.Tombstone.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (key : GoSlice)
    (k : GoString) (rev : Revision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxWriter γ ilog pend ∗ key ↦*□ k ∗
      ⌜mvcc.revOf rev = ⟨W64 ilog.length, W64 pend.length⟩ ∧ 1 ≤ ilog.length ∧
        pend.length + 1 < 2 ^ 63 ∧ mvcc.LogWf' (ilog ++ [pend ++ [.del k]])⌝ }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Tombstone")) (Val #key))
      (Val #rev))
  {{ RET (PairV #(mvcc.liveW (ilog ++ [pend ++ [.del k]]) k - mvcc.liveW (ilog ++ [pend]) k)
        #GoInterface.nil);
      mvcc.idxWriter γ ilog (pend ++ [.del k]) }}

end spec

end EtcdGrove
end Perennial

