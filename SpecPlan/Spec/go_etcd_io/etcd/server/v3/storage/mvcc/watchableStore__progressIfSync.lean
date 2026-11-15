/-
`(*watchableStore).progressIfSync(watchers, id)` (internal): under `s.mu`'s read side, if every
watcher of the map is synced and the store's revision is not below its start, a progress response
`{id, Revision: rev}` sent (without blocking) on the first one's channel; `true` then.

**Proof sketch.** `s.mu.RLock` (the reader token); `s.rev()` (its spec); the checks; `w.send` with no
events (`wsSendable`: a synced watcher's events up to the store's revision were all sent, so
`progStep` holds; for `-1`, every watcher of the stream's map, which `ws.mu` keeps equal to the
registered and not removed ones: the coverage of `wsRespOk`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import SpecPlan.Spec.go_uber_org.zap.Api

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

def watchableStore.progressIfSync.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (ι : WsNames) (m : GoMap) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsMapAt m ι ∗ mvccReaders γ 1 }}
    (App (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"progressIfSync")) (Val #m)) (Val #id))
  {{ (b : Bool), RET #b; wsMapAt m ι ∗ mvccReaders γ 1 }}

end spec

end Mvcc
end EtcdGrove
end Perennial
