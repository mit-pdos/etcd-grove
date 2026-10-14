/-
`clientv3.NewKV(c)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewKV(c)` on a `*Client` with a connection to `K` (`clientKVAt`): a new `*kv` over a
`*retryKVClient` on that connection, with the client's call options (`kvObjAt`), as a `KV`. -/
abbrev NewKV.spec : Prop :=
  ∀ (cl : Loc) (K : KVConn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientKVAt cl K }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewKV)) (Val #cl))
  {{ (v : GoInterface), RET #v; ∃ api : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api⌝ ∗
      kvObjAt api K }}

end spec

end EtcdGrove
end Perennial
