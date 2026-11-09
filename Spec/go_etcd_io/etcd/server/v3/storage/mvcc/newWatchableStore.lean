/-
`newWatchableStore(lg, b, le, cfg)` (internal): `NewStore` (3e) wrapped as a watchable store, its
views and the lessor's range deleter set to it; the loops not started.

**Proof sketch.** `zap.NewNop()` for a `nil` logger; `NewStore` (3e's `NewStore.spec`); the struct
(`victimc` buffered 1, the two groups `newWatcherGroup`, `stopc`); the views (`readView`,
`writeView`: 3e's); `le.SetRangeDeleter(func() { return s.Write(TODO) })` when `le` is not `nil`
(3c's; the deleter's contract `KV.Write.contract` at `*watchableStore`, `mvccDeleter`); the watch
invariant allocated (`wsInv`: empty groups, no victim, `mvccLb`'s authority at `h`) and the loops'
shares (two of the store's reader slots, parked by `NewStore`; their wait-group deposits due once
`New` ran `wg.Add(2)`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def newWatchableStore.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (le : Loc) (cfg : StoreConfig) (B : MvccStorage)
    (Pk : IProp GF) (h : EtcdModel.KVHist) (u : Bool) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat)
    (ls : Lease.LessorState) (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ ⌜storeCfgOk cfg⌝ ∗
      mvccStorageFor B Pk h u ∗ ⌜MvccReachable ⟨h, []⟩⌝ ∗
      storageHook B dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
      Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y ∗
      Lease.isLessor le γl c ∗ Lease.lessorState γl n ls }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore)) (Val #lg))
      (Val #(GoInterface.ok (storageVal B)))) (Val #(Lease.lessorIface le))) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : MvccName, wsInv s γ ∗ mvccLessorIs γ γl ∗
      mvccState γ ⟨h, []⟩ ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccTokN ∗
      storageHook B dq f ∗ (if u then iprop(Post ∗ Y) else iprop(Pre ∗ X)) ∗
      (∃ (rd : GoFunc) (n' : Nat) (ls' : Lease.LessorState), mvccDeleter rd γ ∗
        ⌜RestoreLs { ls with rd := rd } h.store ls'⌝ ∗ Lease.lessorState γl n' ls') ∗
      wsLoopS s γ ∗ wsLoopV s γ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
