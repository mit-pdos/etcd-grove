/-
## `newPeerStatus(lg, local, id)`

**Users.** `startPeer`, `startRemote`.

**Proof sketch.** The literal (`zap.NewNop()` for a `nil` logger); its mutex invariant.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) A new, inactive peer status. -/
def newPeerStatus.spec : Prop :=
  ∀ (lg : Loc) (lcl id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newPeerStatus)) (Val #lg)) (Val #lcl)) (Val #id))
  {{ (s : Loc), RET #s; statusAt s }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
