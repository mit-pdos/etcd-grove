/-
`treeIndex.Revisions` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `ti.Revisions(key, end, atRev, limit, withTotalCount)` by a reader with the certificate of
a committed log `log`, at a revision below its length: the revisions of the keys of `[key, end)`
(`end == nil`: the one key) that `log` determines at `atRev`, in key order, at most `limit` of
them if positive, and their count (all of them if `withTotalCount`, else at most `limit`). -/
abbrev mvcc.treeIndex.Revisions.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (log : mvcc.Log) (key endk : GoSlice) (k e : GoString)
    (atRev limit : w64) (withTotal : Bool) (e0 : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxReader ti γ ∗ mvcc.idxCert γ log ∗
      ⌜0 ≤ sint.Z atRev ∧ sint.Z atRev < log.length⌝ ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e0 }}
    (App (App (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Revisions"))
      (Val #key)) (Val #endk)) (Val #atRev)) (Val #limit)) (Val #withTotal))
  {{ (revs : GoSlice) (total : w64), RET (PairV #revs #total);
      mvcc.idxReader ti γ ∗
      revs ↦* ((mvcc.rangeTaken log (decide (endk = slice.nil)) k e atRev limit).map
        fun x => mvcc.revVal x.2.1) ∗
      ownSliceCap Revision revs (DFrac.own 1) ∗
      ⌜total = W64 (mvcc.rangeTotal log (decide (endk = slice.nil)) k e atRev limit withTotal)⌝ }}

end spec

end EtcdGrove
end Perennial
