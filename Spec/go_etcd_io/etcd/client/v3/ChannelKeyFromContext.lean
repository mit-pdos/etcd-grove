/-
`ChannelKeyFromContext(ctx)` (`client/v3/channel_key.go:43`, PR #21765): returns the explicit
channel key from `ctx` (`""` if absent). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.channelKeyFromContext

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

/-- `ChannelKeyFromContext(ctx)` on a context carrying `o` (`clientv3.ctxChannelKeyIs ctx o`)
returns `o.getD ""`. -/
abbrev ChannelKeyFromContext.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      clientv3.ctxChannelKeyIs ctx o }}
    (App (Val (@! go_etcd_io.etcd.client.v3.ChannelKeyFromContext)) (Val #ctx))
  {{ (key : GoString), RET #key; ⌜key = o.getD go!""⌝ }}

end spec

end EtcdGrove
end Perennial
