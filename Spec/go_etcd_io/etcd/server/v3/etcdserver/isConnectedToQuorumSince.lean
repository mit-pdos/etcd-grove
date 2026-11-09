/-
## `isConnectedToQuorumSince(transport, since, self, members)` (`util.go:28-30`)

**Users.** `parseProposeCtxErr` (2c: which timeout error to return).

**Proof sketch.** `numConnectedSince`, `quorum`.

**Changes**: from `specs-ref`'s `isConnectedToQuorumSince.lean`. **Margin.** Any answer.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`isConnectedToQuorumSince`**: some answer. -/
def isConnectedToQuorumSince.spec : Prop :=
  ∀ (tp : GoInterface) (ν : Rafthttp.Net GF) (lid : w64) (since : time.Time) (self : w64) (sl : GoSlice) (ms : List Member),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ Rafthttp.transporterOk tp ν lid ∗ Membership.membersOwn sl ms ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.isConnectedToQuorumSince)) (Val #tp)) (Val #since)) (Val #self)) (Val #sl))
  {{ (b : Bool), RET #b; Membership.membersOwn sl ms ∗ threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
