/-
`c.dialSetupOpts(creds, dopts...)` (`client/v3/client.go`; item 5): the dial options before
authentication, with the client's interceptors. Lean-first (no Rocq counterpart).
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

/-- `c.dialSetupOpts(creds, dopts...)` on a client `New` builds (`retryClientOk`; its
configuration `cfg`, read-only, with no keepalive), with the options `ds` (`dopts`): `dopts`, then
transport credentials (`creds`, or insecure ones), etcd's stream interceptor and the retry
interceptor (`etcdInterceptorOk`), in a new slice. -/
abbrev Client.dialSetupOpts.spec : Prop :=
  ∀ (c : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (cr : GoInterface) (sl : GoSlice)
    (ds : List GrpcDialOpt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"cfg" ↦□ cfg ∗ ⌜sint.Z cfg.DialKeepAliveTime' ≤ 0⌝ ∗
      dialOptsAt sl ds }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialSetupOpts")) (Val #cr)) (Val #sl))
  {{ (osl : GoSlice), RET #osl; ∃ (si ic : GoFunc),
      dialOptsAt osl (ds ++ [.transportCreds, .streamInterceptor si, .unaryInterceptor ic]) ∗
      ownSliceCap GoInterface osl (DFrac.own 1) ∗ ⌜etcdStreamInterceptor si⌝ ∗
      etcdInterceptorOk ic ∗
      -- (2026-10-19, D21 M6, D21i) a client configured for one attempt (`MaxUnaryRetries: 1`)
      (⌜cfg.MaxUnaryRetries' = W64 1⌝ -∗ etcdInterceptorOk1 ic) }}

end spec

end EtcdGrove
end Perennial
