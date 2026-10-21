/-
`c.dialWithBalancer(dopts...)` (`client/v3/client.go`, names only: its body is a trusted unfolding,
`Proof/go_etcd_io/etcd/client/v3/DialWithBalancerBody.lean`; item 5). Lean-first (no Rocq
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

/-- `c.dialWithBalancer()` on a client `New` builds (`retryClientOk`; its configuration `cfg` with
no keepalive and no dial options of the caller's; no token bundle; its credentials, read-only;
its endpoints `eps`, read-only, plain, at least one (D27); its resolver, not dialed, with them):
an etcd connection to the servers at `eps` (`isEtcdConn`), or an error. -/
abbrev Client.dialWithBalancer.spec : Prop :=
  ∀ (c : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (cr : GoInterface) (r : Loc)
    (esl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"cfg" ↦□ cfg ∗ ⌜sint.Z cfg.DialKeepAliveTime' ≤ 0⌝ ∗
      cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
      clientF c go!"authTokenBundle" ↦□ GoInterface.nil ∗ clientF c go!"creds" ↦□ cr ∗
      clientF c go!"endpoints" ↦□ esl ∗ esl ↦*□ eps ∗ ⌜plainEndpoints eps⌝ ∗
      clientF c go!"resolver" ↦□ r ∗ etcdResolverOwn r eps }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialWithBalancer")) (Val #slice.nil))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      (⌜err = GoInterface.nil⌝ ∗ isEtcdConn conn eps ∗
        -- (2026-10-19, D21 M6) configured for one attempt
        (⌜cfg.MaxUnaryRetries' = W64 1⌝ -∗ isEtcdConn1 conn eps)) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
