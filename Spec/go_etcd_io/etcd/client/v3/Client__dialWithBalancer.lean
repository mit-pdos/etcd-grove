/-
`c.dialWithBalancer(dopts...)` and `c.dialWithBalancerForKey(ctx, key, r, endpoints, dopts...)`
(`client/v3/client.go`; item 5, updated for PR #21765). `dialWithBalancerForKey`'s body is a
trusted unfolding (`Proof/go_etcd_io/etcd/client/v3/DialWithBalancerBody.lean`); `dialWithBalancer`
is translated by Goose and delegates to `dialWithBalancerForKey`. Lean-first (no Rocq counterpart).
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
no dial options of the caller's; no token bundle; its credentials, read-only; its `ctx` field;
its endpoints `eps`, read-only, plain, at least one (D27); its resolver, not dialed, with them):
an etcd connection to the servers at `eps` (`isEtcdConn`, `conn ≠ null`), or an error. -/
abbrev Client.dialWithBalancer.spec : Prop :=
  ∀ (c : Loc) (ctx : GoInterface) (dq : DFrac) (cfg : go_etcd_io.etcd.client.v3.Config)
    (cr : GoInterface) (r : Loc) (esl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"ctx" ↦{dq} ctx ∗ clientF c go!"cfg" ↦□ cfg ∗
      cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
      clientF c go!"authTokenBundle" ↦□ GoInterface.nil ∗ clientF c go!"creds" ↦□ cr ∗
      clientF c go!"endpoints" ↦□ esl ∗ esl ↦*□ eps ∗ ⌜plainEndpoints eps⌝ ∗
      clientF c go!"resolver" ↦□ r ∗ etcdResolverOwn r eps }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialWithBalancer")) (Val #slice.nil))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      clientF c go!"ctx" ↦{dq} ctx ∗
      ((⌜err = GoInterface.nil ∧ conn ≠ null⌝ ∗ isEtcdConn conn eps) ∨ ⌜err ≠ GoInterface.nil⌝) }}

/-- `c.dialWithBalancerForKey(ctx, key, r, esl)` on a client `New` builds (`retryClientOk`; its
configuration `cfg` with no dial options of the caller's; no token bundle; its credentials,
read-only), with plain endpoints `eps` (at least one, in `esl`) and a fresh resolver `r` with them:
an etcd connection to the servers at `eps` (`isEtcdConn`, `conn ≠ null`), or an error (giving back
`esl ↦*{dq} eps`). -/
abbrev Client.dialWithBalancerForKey.spec : Prop :=
  ∀ (c : Loc) (ctx : GoInterface) (key : GoString) (cfg : go_etcd_io.etcd.client.v3.Config)
    (cr : GoInterface) (r : Loc) (esl : GoSlice) (dq : DFrac) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"cfg" ↦□ cfg ∗
      cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
      clientF c go!"authTokenBundle" ↦□ GoInterface.nil ∗ clientF c go!"creds" ↦□ cr ∗
      esl ↦*{dq} eps ∗ ⌜plainEndpoints eps⌝ ∗
      etcdResolverOwn r eps }}
    (App (App (App (App (App
      (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialWithBalancerForKey"))
      (Val #ctx)) (Val #key)) (Val #r)) (Val #esl)) (Val #slice.nil))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      esl ↦*{dq} eps ∗
      ((⌜err = GoInterface.nil ∧ conn ≠ null⌝ ∗ isEtcdConn conn eps) ∨ ⌜err ≠ GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
