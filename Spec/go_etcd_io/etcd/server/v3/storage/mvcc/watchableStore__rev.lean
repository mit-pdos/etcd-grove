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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.rev()`: the inner store's revision (`store.Rev`, through its read view, which reads the
watchable store): the last revision of a committed log, which extends the initial one (so the
revision is at least `1`: `isStore`'s certificate); with a lent fraction of the committed log's
authority (`logLent`, unit W-K: `progressIfSync`'s, under `s.mu`), that log. Of a store that may be compacted
(`storeReaderC`; 2026-10-13, unit 6a); the frozen statement (`storeReader`) is `specFrozen`
(`spec_frozen`, `FrozenSpecs.lean`). -/
abbrev mvcc.watchableStore.rev.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (oa : Option (Qp × mvcc.Log)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.storeReaderC st γ.st ∗ mvcc.logLent γ.st.idx oa }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"rev")) (Val #()))
  {{ (r : w64), RET #r; mvcc.storeReaderC st γ.st ∗ mvcc.logLent γ.st.idx oa ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.st.idx log ∗ ⌜log ≠ [] ∧ r = W64 ((log.length : Int) - 1) ∧
        2 ≤ log.length ∧ log.length < 2 ^ 63 ∧ ∀ q L, oa = some (q, L) → log = L⌝ }}

end spec

end EtcdGrove
end Perennial
