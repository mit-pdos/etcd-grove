/-
# Membership's error values as the server's sentinels (second pass)

`toGRPCErrorMap` (`v3rpc/util.go:36-41`) maps membership's six error variables to the server's
gRPC errors; server-core's encoding is `EtcdServer.sentinelAt g e` (the global `g` holds, read-only,
a value `srvErr` names for the `EtcdErr` `e`). This law gives membership's in that encoding
(server-core's request 3). A separate module because `membership/Api.lean` cannot import
`etcdserver/errors/Api.lean` (that module reaches `storage/schema`, which imports membership's).

`init.spec` (`Api.lean`: the values pairwise distinct, non-`nil`) stays the package's own law; this
one adds what the server's error mapping needs. `ErrIDRemoved` and `ErrIDNotFound` both map to
`memberNotFound` (two distinct values, one `EtcdErr`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.errors.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Membership

open Iris Iris.BI EtcdModel

/-- The server's error each validation error maps to (`toGRPCErrorMap`). -/
def VErr.etcd : VErr → EtcdErr
  | .idRemoved => .memberNotFound
  | .idNotFound => .memberNotFound
  | .memberNotLearner => .memberNotLearner
  | .idExists => .memberExist
  | .peerURLExists => .peerURLExist
  | .tooManyLearners => .tooManyLearners

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **Membership's error variables are the server's sentinels** of their mapped errors. -/
def errs_srv.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ⊢
    □ ∀ e : VErr, EtcdServer.sentinelAt e.global e.etcd

end laws

end Membership
end EtcdGrove
end Perennial
