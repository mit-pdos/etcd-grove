/-
`readView__FirstRev` (metrics_txn.go / kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `rv.FirstRev()`: a read transaction opened and closed; the compaction revision it observed
(`store.Read`'s `firstRev`), at or above the caller's lower bound `c` (2026-10-13, unit 6a). The
frozen statement (`storeReader`, `-1`) is `specFrozen` (`spec_frozen`, `FrozenSpecs.lean`). -/
abbrev mvcc.readView.FirstRev.spec : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReaderC s γ ∗ mvcc.crevLb γ.idx c }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"FirstRev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReaderC s γ ∗
      ∃ crev : Int, mvcc.crevLb γ.idx crev ∗ ⌜v = W64 crev ∧ c ≤ crev ∧ -1 ≤ crev⌝ }}

end spec

end EtcdGrove
end Perennial
