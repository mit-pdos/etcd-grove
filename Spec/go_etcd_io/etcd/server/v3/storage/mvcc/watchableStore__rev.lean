/-
`watchableStore.rev` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

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

/-- `s.rev()`: the inner store's revision (`store.Rev`, through its read view, which reads the
watchable store): the last revision of a committed log. Of a store that may be compacted
(`storeReaderC`; 2026-10-13, unit 6a); the frozen statement (`storeReader`) is `specFrozen`
(`spec_frozen`, `FrozenSpecs.lean`). -/
abbrev mvcc.watchableStore.rev.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.storeReaderC st γ.st }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"rev")) (Val #()))
  {{ (r : w64), RET #r; mvcc.storeReaderC st γ.st ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.st.idx log ∗ ⌜log ≠ [] ∧ r = W64 ((log.length : Int) - 1)⌝ }}

end spec

end EtcdGrove
end Perennial
