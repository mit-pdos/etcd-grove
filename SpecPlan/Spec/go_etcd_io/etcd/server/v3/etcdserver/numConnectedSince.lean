/-
## `numConnectedSince(transport, since, self, members)` (`util.go:78-88`)

**Users.** `isConnectedToQuorumSince` (2c).

**Proof sketch.** A loop over the members' pointers (`Membership.membersOwn` at any fraction: the
ids read), `isConnectedSince` per member.

**Changes**: from `specs-ref`'s `numConnectedSince.lean`. **Margin.** Any count up to the length.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **`numConnectedSince`**: at most the number of members. -/
def numConnectedSince.spec : Prop :=
  ∀ (tp : GoInterface) (ν : Rafthttp.Net GF) (lid : w64) (since : time.Time) (self : w64) (sl : GoSlice) (ms : List Member),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ Rafthttp.transporterOk tp ν lid ∗ Membership.membersOwn sl ms ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.numConnectedSince)) (Val #tp)) (Val #since)) (Val #self)) (Val #sl))
  {{ (k : w64), RET #k; Membership.membersOwn sl ms ∗ threadTok ∗ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ms.length⌝ }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
