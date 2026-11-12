/-
`c.dialSetupOpts(creds, dopts...)` (`client/v3/client.go`; item 5): the dial options before
authentication, with the client's interceptors. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
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

/-- `c.dialSetupOpts(creds, dopts...)` on a client `New` builds (`retryClientOk`; its
configuration `cfg`, read-only), with the options `ds` (`dopts`): grpc's keepalive option if
`cfg.DialKeepAliveTime` is positive (`kaOpts`, D28), `dopts`, then transport credentials (`creds`, or insecure ones), etcd's stream interceptor and the retry
interceptor (`etcdInterceptorOkG`: its contract once the client is ready), in a new slice. -/
abbrev Client.dialSetupOpts.spec : Prop :=
  ∀ (c : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (cr : GoInterface) (sl : GoSlice)
    (ds : List GrpcDialOpt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"cfg" ↦□ cfg ∗
      dialOptsAt sl ds }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialSetupOpts")) (Val #cr)) (Val #sl))
  {{ (osl : GoSlice), RET #osl; ∃ (si ic : GoFunc),
      dialOptsAt osl (kaOpts cfg ++ ds ++ [.transportCreds, .streamInterceptor si, .unaryInterceptor ic]) ∗
      ownSliceCap GoInterface osl (DFrac.own 1) ∗ ⌜etcdStreamInterceptor si⌝ ∗
      -- (the auth plan's C1, 2026-10-28) gated on the client's readiness (D29: both modes)
      etcdInterceptorOkG c ic }}

end spec

end EtcdGrove
end Perennial
