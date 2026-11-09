/-
`(*watchableStore).moveVictims()` (internal): resends each victim's pending response (outside
`s.mu`), then under `s.mu` and `revMu` puts each watcher whose send succeeded back in a group
(unsynced if its `minRev` is at or below the current revision, else synced); the failed ones stay
victims. Returns how many were moved.

**Proof sketch.** Under `s.mu`: the victims taken (each batch with its watchers' `wsSendable`
responses: `Revision` `minRev - 1`); `w.send` (its spec) for each; under `s.mu` and `revMu.RLock`
(the loop's reader, `wsLoopV`) each record updated, `unsynced.add`/`synced.add`; the failed ones
appended to `victims` again.
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

def watchableStore.moveVictims.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsLoopV s γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"moveVictims")) (Val #()))
  {{ (moved : w64), RET #moved; wsLoopV s γ ∗ ⌜0 ≤ sint.Z moved⌝ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
