/-
`channelKeyFromContext(ctx)` (`client/v3/channel_key.go:56`, PR #21765): extracts the explicit
channel key from `ctx` (`("", false)` if `ctx == nil` or no string value is stored under
`channelKeyContextKey{}`, `(k, true)` if `k` is stored). Lean-first (no Rocq counterpart).
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

/-- `channelKeyFromContext(ctx)` on a context carrying `o` (`clientv3.ctxChannelKeyIs ctx o`)
returns `(o.getD "", o.isSome)`. -/
abbrev channelKeyFromContext.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      clientv3.ctxChannelKeyIs ctx o }}
    (App (Val (@! go_etcd_io.etcd.client.v3.channelKeyFromContext)) (Val #ctx))
  {{ (key : GoString) (ok : Bool), RET (PairV #key #ok);
      ⌜key = o.getD go!"" ∧ ok = o.isSome⌝ }}

end spec

end EtcdGrove
end Perennial
