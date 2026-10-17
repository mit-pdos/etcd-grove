/-
`c.dial(creds, dopts...)` (`client/v3/client.go`; item 5): the dial. Lean-first (no Rocq
counterpart).
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

/-- `c.dial(creds, dopts...)` on a client `New` builds (`retryClientOk`; its configuration
`cfg` with no keepalive and no dial options of the caller's; no token bundle; its endpoints
`[ep]`, read-only, a plain one), with the one option `WithResolvers(rb)` of a resolver of etcd's scheme to
`ep` (taken): an etcd connection to the server at `ep` (`isEtcdConn`: the retry interceptor
installed), or an error. -/
abbrev Client.dial.spec : Prop :=
  ∀ (c : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (cr : GoInterface) (sl : GoSlice)
    (rb : GoInterface) (esl : GoSlice) (ep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientNewVars ∗
      retryClientOk c ∗ clientF c go!"cfg" ↦□ cfg ∗ ⌜sint.Z cfg.DialKeepAliveTime' ≤ 0⌝ ∗
      cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
      clientF c go!"authTokenBundle" ↦□ GoInterface.nil ∗
      clientF c go!"endpoints" ↦□ esl ∗ esl ↦*□ [ep] ∗ ⌜plainEndpoint ep⌝ ∗
      dialOptsAt sl [.resolvers [rb]] ∗ grpcResolverAt rb etcdScheme ep }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dial")) (Val #cr)) (Val #sl))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      (⌜err = GoInterface.nil⌝ ∗ isEtcdConn conn ep) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
