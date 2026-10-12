/-
`treeIndex.CountRevisions` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
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

/-- `ti.CountRevisions(key, end, atRev)`, for a reader with the knowledge `kn` of the index
(`idxKnows`: a committed log's certificate, or the writer's handle; its log `log := kn.log`)
and `atRev` below its length: the number of keys of `[key, end)` (the one `key` if
`end == nil`) with a revision at `atRev` in `log`. -/
abbrev mvcc.treeIndex.CountRevisions.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (kn : mvcc.IdxKnow) (key endk : GoSlice) (k e : GoString)
    (atRev : w64) (e0 : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗
      ⌜0 ≤ sint.Z atRev ∧ sint.Z atRev < kn.log.length⌝ ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e0 }}
    (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"CountRevisions"))
      (Val #key)) (Val #endk)) (Val #atRev))
  {{ RET #(W64 (mvcc.rangeAnswers kn.log (decide (endk = slice.nil)) k e atRev).length);
      mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn }}

end spec

end EtcdGrove
end Perennial
