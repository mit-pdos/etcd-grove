/-
`treeIndex.Get` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
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

/-- `ti.Get(key, atRev)` by a reader with the knowledge `kn` of the index
(`idxKnows`: a committed log's certificate, or the writer's handle; its log `kn.log`), at a revision below its length: what `log` determines of the key (`kiGetVal` of the key's index
built from `log`'s events: its revision, create revision and version at `atRev`, or
`ErrRevisionNotFound`). The reader holds a part of the compaction revision `c`'s authority (`crevUB`, given back),
at or below `atRev`: every key's compaction level is at most `c` (`idxLockInv`). -/
abbrev mvcc.treeIndex.Get.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (kn : mvcc.IdxKnow) (key : GoSlice) (k : GoString)
    (atRev : w64) (e : GoInterfaceOk) (q : Qp) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗
      mvcc.crevUB γ q c ∗ ⌜-1 ≤ c ∧ c ≤ sint.Z atRev⌝ ∗
      ⌜0 ≤ sint.Z atRev ∧ sint.Z atRev < kn.log.length⌝ ∗ key ↦*□ k ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Get")) (Val #key))
      (Val #atRev))
  {{ RET (mvcc.kiGetVal (mvcc.kiOfKey (mvcc.evsOf kn.log) k) atRev (GoInterface.ok e));
      mvcc.idxReader ti γ ∗ mvcc.idxKnows γ kn ∗ mvcc.crevUB γ q c ∗ key ↦*□ k }}

end spec

end EtcdGrove
end Perennial

