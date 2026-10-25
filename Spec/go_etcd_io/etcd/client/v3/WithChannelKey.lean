/-
`WithChannelKey(ctx, key)` (`client/v3/channel_key.go:38`, PR #21765): wraps `ctx` with
`context.WithValue(ctx, channelKeyContextKey{}, key)`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.WithValue

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

/-- `WithChannelKey(ctx, key)` returns a context derived from `ctx` (`context.isContext`) whose
`Value(channelKeyContextKey{})` returns `key` (`clientv3.ctxChannelKeyIs ctx' (some key)`). -/
abbrev WithChannelKey.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      context.isContext ctx cd }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.WithChannelKey)) (Val #(GoInterface.ok ctx)))
      (Val #key))
  {{ (ctx' : GoInterface), RET #ctx'; ∃ (ci : GoInterfaceOk) (vs : GMap GoInterface GoInterface),
      ⌜ctx' = GoInterface.ok ci⌝ ∗ context.isContext ci { cd with Values := vs } ∗
      clientv3.ctxChannelKeyIs ctx' (some key) }}

end spec

end EtcdGrove
end Perennial
