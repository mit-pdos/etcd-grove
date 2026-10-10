/-
`treeIndex.Range` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
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

/-- The `keys` of a range read: a slice of the keys' slices (`ki.key`, read-only), each
holding its key. -/
def mvcc.ownKeys (keys : GoSlice) (ks : List GoString) : IProp GF :=
  iprop(∃ kss : List GoSlice, keys ↦* kss ∗ ownSliceCap GoSlice keys (DFrac.own 1) ∗
    ⌜kss.length = ks.length⌝ ∗ [∗list] p ∈ kss.zip ks, p.1 ↦*□ p.2)

/-- `ti.Range(key, end, atRev, limit, withTotalCount)`, for a reader holding the certificate of
a committed `log` and `atRev` below its length: the keys of `[key, end)` (the one `key` if
`end == nil`) with a revision at `atRev` in `log`, in key order, with their modified and
created revisions and versions, at most `limit` of them if positive (`rangeTaken`), and the
count (`rangeTotal`: all of them if `withTotalCount`, else at most `limit`). -/
abbrev mvcc.treeIndex.Range.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (log : mvcc.Log) (key endk : GoSlice) (k e : GoString)
    (atRev limit : w64) (withTotal : Bool) (e0 : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxReader ti γ ∗ mvcc.idxCert γ log ∗
      ⌜0 ≤ sint.Z atRev ∧ sint.Z atRev < log.length⌝ ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e0 }}
    (App (App (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Range"))
      (Val #key)) (Val #endk)) (Val #atRev)) (Val #limit)) (Val #withTotal))
  {{ (keys modifies creates vers : GoSlice) (total : w64),
      RET (PairV (PairV (PairV (PairV #keys #modifies) #creates) #vers) #total);
      mvcc.idxReader ti γ ∗
      mvcc.ownKeys keys ((mvcc.rangeTaken log (decide (endk = slice.nil)) k e atRev limit).map
        Prod.fst) ∗
      modifies ↦* ((mvcc.rangeTaken log (decide (endk = slice.nil)) k e atRev limit).map
        fun x => mvcc.revVal x.2.1) ∗
      ownSliceCap Revision modifies (DFrac.own 1) ∗
      creates ↦* ((mvcc.rangeTaken log (decide (endk = slice.nil)) k e atRev limit).map
        fun x => mvcc.revVal x.2.2.1) ∗
      ownSliceCap Revision creates (DFrac.own 1) ∗
      vers ↦* ((mvcc.rangeTaken log (decide (endk = slice.nil)) k e atRev limit).map
        fun x => x.2.2.2) ∗
      ownSliceCap w64 vers (DFrac.own 1) ∗
      ⌜total = W64 (mvcc.rangeTotal log (decide (endk = slice.nil)) k e atRev limit withTotal)⌝ }}

end spec

end EtcdGrove
end Perennial
