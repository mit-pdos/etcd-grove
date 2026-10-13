/-
`readView__Rev` (metrics_txn.go / kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `rv.Rev()`: a read transaction opened and closed; the last revision of a committed log. Of
a store that may be compacted (`storeReaderC`; 2026-10-13, unit 6a); the frozen statement
(`storeReader`) is `specFrozen` (`spec_frozen`, `FrozenSpecs.lean`). -/
abbrev mvcc.readView.Rev.spec : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReaderC s γ }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Rev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReaderC s γ ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜log ≠ [] ∧ v = W64 ((log.length : Int) - 1)⌝ }}

end spec

end EtcdGrove
end Perennial
