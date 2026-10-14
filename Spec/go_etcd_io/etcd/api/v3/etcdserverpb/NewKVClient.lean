/-
`etcdserverpb.NewKVClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated KV stub;
translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
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

/-- `NewKVClient(cc)`: a new `*kVClient` whose `cc` is `cc` (read-only), as a `KVClient`. -/
abbrev NewKVClient.spec : Prop :=
  ∀ (cc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }}
    (App (Val (@! etcdserverpb.NewKVClient)) (Val #cc))
  {{ (v : GoInterface), RET #v; ∃ kc : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType etcdserverpb.kVClient.ty) #kc⌝ ∗
      structFieldRef etcdserverpb.kVClient go!"cc" kc ↦□ cc }}

end spec

end EtcdGrove
end Perennial
