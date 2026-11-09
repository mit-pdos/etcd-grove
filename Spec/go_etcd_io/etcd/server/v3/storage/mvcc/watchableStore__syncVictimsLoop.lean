/-
`(*watchableStore).syncVictimsLoop()` (internal, a goroutine of `New`): `moveVictims` until it moves
nothing, then waits for a victim, 10ms when victims remain, or `stopc`.

**Proof sketch.** Loop invariant `wsLoopV s γ`; `moveVictims` (its spec); `s.mu.RLock` (the loop's
reader); `time.After` (Perennial's `time`); the `select` (`victimc`'s receive; `stopc` closed: `Done`
deposits the loop's reader).
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

def watchableStore.syncVictimsLoop.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsLoopV s γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"syncVictimsLoop")) (Val #()))
  {{ RET #(); True }}

end spec

end Mvcc
end EtcdGrove
end Perennial
