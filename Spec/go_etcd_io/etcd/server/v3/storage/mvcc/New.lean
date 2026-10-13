/-
`New` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

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

/-- `New(lg, b, le, cfg)` on a fresh backend (`newWatchableStore`'s premises): the watchable store
as a `WatchableKV`, its two loops started (`s.wg.Add(2)`, each with a reader slot and a done
token), with what `newWatchableStore` gives (every watch token among it) but those two slots, and the right to close it
(`wsCloser`: the stop channel's close, the wait for the loops, the inner store's close). -/
abbrev mvcc.New.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb⌝ →
        mvcc.isKeyBackendG b (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
          (mvcc.storePutOk γ) (mvcc.storeW s γ) (mvcc.kbWi γ.kb) P f) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      mvcc.isLessor le γl }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #s);
      ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧ γ.st.kb = kb⌝ ∗
        mvcc.isWatchableStore s st γ ∗ mvcc.hookIs γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
        mvcc.watchToks γ (2 ^ 63 - 3) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (),
          mvcc.watchReader s st γ) ∗
        mvcc.wsCloser s st }}

end spec

end EtcdGrove
end Perennial
