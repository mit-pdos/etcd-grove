/-
`(*EtcdServer).AuthStore()` (`server.go:2422`): `s.authStore`.

**Users**: v3rpc's `authMaintenanceServer.requireAuthInfo`, `AuthAdmin.isPermitted`,
`serverWatchStream.isWatchPermitted` (their sketches call `AuthStore()`); the snippet
`etcdserverreq/lease.go` `ReqExpiryRevoke` (the root context).

**Proof sketch**: a read of the read-only field (`srvNode`: the auth store `NewServer` built, 3d's
`authStoreAt` at the member's `srvAuth` names, its tokens the cluster's): 3a's `authOk`.

**Changes**: verify round (A7-completeness F3): new here (the old tree's
`EtcdServer__AuthStore.lean`).

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`AuthStore()`**: the member's auth store (3d's `authStoreAt` over the cluster, at the member's
auth names). -/
def EtcdServer.AuthStore.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvNode s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"AuthStore")) (Val #()))
  {{ (ast : GoInterface), RET #ast; ∃ (st : Loc) (γa : Auth.AuthNames),
      ⌜ast = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty) #st⌝ ∗
      Auth.authStoreAt st γ.etcd γa ∗ srvAuth s γa }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
