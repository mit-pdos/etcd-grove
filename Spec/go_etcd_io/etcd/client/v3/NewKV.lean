/-
`clientv3.NewKV(c)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
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

/-- `NewKV(c)` on a `*Client` with the connection `conn` (`clientKVAtS`): a new `*kv` over a
`*retryKVClient` on that connection, with the client's call options (`kvObjS`), as a `KV` (the auth plan's C1, 2026-10-28: without the connection's fact, which `newClient` attaches once
the client is ready, `InvClientAuth.lean`). -/
abbrev NewKV.spec : Prop :=
  ∀ (cl conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientKVAtS cl conn }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewKV)) (Val #cl))
  {{ (v : GoInterface), RET #v; ∃ api : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api⌝ ∗
      kvObjS api conn }}

end spec

end EtcdGrove
end Perennial
