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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `ti.Get(key, atRev)` by a reader with the certificate of a committed log `log`, at a
revision below its length: what `log` determines of the key (`kiGetVal` of the key's index
built from `log`'s events: its revision, create revision and version at `atRev`, or
`ErrRevisionNotFound`). -/
abbrev mvcc.treeIndex.Get.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (log : mvcc.Log) (key : GoSlice) (k : GoString)
    (atRev : w64) (e : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxReader ti γ ∗ mvcc.idxCert γ log ∗
      ⌜0 ≤ sint.Z atRev ∧ sint.Z atRev < log.length⌝ ∗ key ↦*□ k ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Get")) (Val #key))
      (Val #atRev))
  {{ RET (mvcc.kiGetVal (mvcc.kiOfKey (mvcc.evsOf log) k) atRev (GoInterface.ok e));
      mvcc.idxReader ti γ ∗ key ↦*□ k }}

end spec

end EtcdGrove
end Perennial

