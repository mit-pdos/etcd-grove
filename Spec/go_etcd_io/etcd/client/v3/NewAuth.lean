/-
`clientv3.NewAuth(c)` (`client/v3/auth.go`; item 5: `newClient` calls it; translated for the auth
plan's E2h, names only before). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewAuth(c)` on a `*Client` with a connection to `addr` (`clientKVAt`, what `NewKV` reads):
a new `*authClient` over a `*retryAuthClient` on that connection, with the client's call options
(`authObjAt`), as an `Auth`. -/
abbrev NewAuth.spec : Prop :=
  ∀ (c : Loc) (addr : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientKVAt c addr }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewAuth)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ api : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #api⌝ ∗
      authObjAt api addr }}

end spec

end EtcdGrove
end Perennial
