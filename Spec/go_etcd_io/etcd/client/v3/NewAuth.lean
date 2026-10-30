/-
`clientv3.NewAuth(c)` (`client/v3/auth.go`; item 5: `newClient` calls it; translated for the auth
plan's E2h, names only before). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

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

/-- `NewAuth(c)` on a `*Client` with the connection `conn` (`clientKVAtS`, what `NewKV` reads):
a new `*authClient` over a `*retryAuthClient` on that connection, with the client's call options
(`authObjS`), as an `Auth` (the auth plan's C1, 2026-10-28: without the connection's fact, which `newClient` attaches once
the client is ready, `InvClientAuth.lean`). -/
abbrev NewAuth.spec : Prop :=
  ∀ (c conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientKVAtS c conn }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewAuth)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ api : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #api⌝ ∗
      authObjS api conn }}

end spec

end EtcdGrove
end Perennial
