/-
## `isConnectedSince(transport, since, remote)` (`util.go:52-55`)

**Users.** `numConnectedSince`; `parseProposeCtxErr` (2c).

**Proof sketch.** The transporter's `ActiveSince` (2f, `transporterOk`), `time.Time`'s `IsZero`,
`Before` (Perennial).

**Changes**: from `specs-ref`'s `isConnectedSince.lean`. **Margin.** Any answer: time is not
modelled.
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

/-- **`isConnectedSince`**: some answer. -/
def isConnectedSince.spec : Prop :=
  ∀ (tp : GoInterface) (since : time.Time.t) (remote : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ transporterOk tp }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.isConnectedSince)) (Val #tp)) (Val #since)) (Val #remote))
  {{ (b : bool), RET #b; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
