/-
## `(*EtcdServer).waitAppliedIndex()` (internal helper; untranslated, an assumed contract)

Users: `LeaseRenew`, `leaseTimeToLive` (`v3_server.go:514,519,638`). The code: a `select` on
`ApplyWaitCommit()` (the apply-wait list at the committed index), `s.stopping` (`ErrStopped`), a
one-second timer (`ErrTimeoutWaitAppliedIndex`). Changes: new as a spec (the old repository took it
as a names-only contract inside the lease plans). Margin: what `nil` says (the member applied the
committed index it read) is not stated: the callers fire loose lease steps that do not need it.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `nil` or an unsettled error. -/
def EtcdServer.waitAppliedIndex.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"waitAppliedIndex")) (Val #()))
  {{ (err : GoInterface), RET #err; threadTok ∗ ⌜err = GoInterface.nil ∨ srvIndef err⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
