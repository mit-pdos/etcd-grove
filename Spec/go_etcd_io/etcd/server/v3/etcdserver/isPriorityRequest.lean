/-
## `isPriorityRequest(r)` (`util.go:72-74`)

**Users.** `exceedsRequestLimit`.

**Proof sketch.** A nil check and a field read (`irrIsRevoke`, provisional 3h).

**Changes**: from `specs-ref`'s `isPriorityRequest.lean`. **Margin.** Exact.
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

/-- **`isPriorityRequest(r)`**: whether `r` is a lease revocation. -/
def isPriorityRequest.spec : Prop :=
  ∀ (r : Loc) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ irrIsRevoke r b }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.isPriorityRequest)) (Val #r))
  {{ RET #b; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
