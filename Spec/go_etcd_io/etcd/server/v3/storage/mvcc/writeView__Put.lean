/-
`writeView.Put` (kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

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

/-- `wv.Put(key, value, lease)`: a write transaction of one put, committed: the new revision
(`ilog`'s length, for the committed log `ilog` the transaction found) is certified. Under the
batch lock, by the critical-section contract (`csContract`: the store's hook on `Pre`, the
caller's update to `Post` before `Unlock`). -/
abbrev mvcc.writeView.Put.spec : Prop :=
  ∀ (wv s : Loc) (γ : mvcc.StoreNames) (P Pre Q Post : IProp GF) (f : val)
    (key value : GoSlice) (k v : GoString) (leaseID : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWriteView wv s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗
      mvcc.hookIs γ P f ∗ mvcc.csContract P f Pre Q Post ∗ key ↦*□ k ∗
      value ↦*□ v ∗ (⌜leaseID = W64 0⌝ ∨ mvcc.leaseKnown γ.leases leaseID) }}
    (App (App (App (Val (wv @!! go.GoType.PointerType writeView.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ (rev : w64), RET #rev; mvcc.storeReader s γ ∗ Post ∗
      ∃ ilog : mvcc.Log, mvcc.idxCert γ.idx (ilog ++ [[.put k v leaseID]]) ∗
        ⌜rev = W64 (ilog.length : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
