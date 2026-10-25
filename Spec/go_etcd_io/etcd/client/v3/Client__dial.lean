/-
`c.dialWithContext(ctx, key, targetEndpoint, creds, dopts...)` (`client/v3/client.go:344`; item 5,
updated for PR #21765): the dial for a channel key. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

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

/-- `c.dialWithContext(ctx, key, targetEndpoint, creds, dopts...)` on a client `New` builds
(`retryClientOk`; its configuration `cfg` with no dial options of the caller's; no token bundle),
with a plain `targetEndpoint` and the one option `WithResolvers(rb)` of a resolver of etcd's scheme
to `eps` (taken): an etcd connection to the servers at `eps` (`isEtcdConn`: the retry interceptor
installed, `conn ≠ null`), or an error. -/
abbrev Client.dial.spec : Prop :=
  ∀ (c : Loc) (ctx : GoInterface) (key targetEndpoint : GoString)
    (cfg : go_etcd_io.etcd.client.v3.Config) (cr : GoInterface) (sl : GoSlice)
    (rb : GoInterface) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"cfg" ↦□ cfg ∗
      cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
      clientF c go!"authTokenBundle" ↦□ GoInterface.nil ∗
      ⌜plainEndpoint targetEndpoint⌝ ∗
      dialOptsAt sl [.resolvers [rb]] ∗ grpcResolverAt rb etcdScheme eps }}
    (App (App (App (App (App
      (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialWithContext"))
      (Val #ctx)) (Val #key)) (Val #targetEndpoint)) (Val #cr)) (Val #sl))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      (⌜err = GoInterface.nil ∧ conn ≠ null⌝ ∗ isEtcdConn conn eps) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
