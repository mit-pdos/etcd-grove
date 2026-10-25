/-
`channelKeyForRequest(ctx)` (`client/v3/channel_key.go:48`, PR #21765): returns `"default"` when
`ChannelKeyFromContext(ctx)` is `""` or `"default"`, and the context's channel key otherwise.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ChannelKeyFromContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `channelKeyForRequest(ctx)` on a context carrying `o` (`clientv3.ctxChannelKeyIs ctx o`)
returns `clientv3.reqChannelKey o`. -/
abbrev channelKeyForRequest.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      clientv3.ctxChannelKeyIs ctx o }}
    (App (Val (@! go_etcd_io.etcd.client.v3.channelKeyForRequest)) (Val #ctx))
  {{ (key : GoString), RET #key; ⌜key = clientv3.reqChannelKey o⌝ }}

end spec

end EtcdGrove
end Perennial
