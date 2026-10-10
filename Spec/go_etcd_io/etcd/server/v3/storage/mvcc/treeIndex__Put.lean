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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `ti.Put(key, rev)` by the writer, for the next change of the pending revision (a put of
`key`, with any value and lease, keeping the log well formed): the key's index gets the
revision (a fresh index if it has none), and the writer's log has the change. The key's bytes
are read-only for good (the index keeps them). -/
abbrev mvcc.treeIndex.Put.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (key : GoSlice)
    (k : GoString) (rev : Revision) (v : GoString) (l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxWriter γ ilog pend ∗ key ↦*□ k ∗
      ⌜mvcc.revOf rev = ⟨W64 ilog.length, W64 pend.length⟩ ∧ 1 ≤ ilog.length ∧
        pend.length + 1 < 2 ^ 63 ∧ mvcc.LogWf' (ilog ++ [pend ++ [.put k v l]])⌝ }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Put")) (Val #key)) (Val #rev))
  {{ RET #(); mvcc.idxWriter γ ilog (pend ++ [.put k v l]) }}

end spec

end EtcdGrove
end Perennial

