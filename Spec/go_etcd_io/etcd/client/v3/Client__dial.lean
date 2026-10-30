/-
`c.dial(creds, dopts...)` (`client/v3/client.go`; item 5): the dial. Lean-first (no Rocq
counterpart).
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

/-- `c.dial(creds, dopts...)` on a client `New` builds (`retryClientOk`; its configuration
`cfg` with no dial options of the caller's; its token bundle, if any, read-only, with
its tokens `""` or meeting `P` (`tokenBundleInv`); its endpoints
`eps`, read-only, plain, at least one, D27), with the one option `WithResolvers(rb)` of a resolver of
etcd's scheme to `eps` (taken): an etcd connection to the servers at `eps` (`isEtcdConnG`: the retry interceptor installed,
its contract once the client is ready), whose attempts carry no credentials' token or one meeting
`P` (`connTokOk`, the auth plan's C1), or an error. -/
abbrev Client.dial.spec : Prop :=
  ∀ (c : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (cr : GoInterface) (sl : GoSlice)
    (rb : GoInterface) (esl : GoSlice) (eps : List GoString) (atb : GoInterface)
    (P : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"cfg" ↦□ cfg ∗
      cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
      clientF c go!"authTokenBundle" ↦□ atb ∗ (⌜atb = GoInterface.nil⌝ ∨ tokenBundleInv atb P) ∗
      clientF c go!"endpoints" ↦□ esl ∗ esl ↦*□ eps ∗ ⌜plainEndpoints eps⌝ ∗
      dialOptsAt sl [.resolvers [rb]] ∗ grpcResolverAt rb etcdScheme eps }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dial")) (Val #cr)) (Val #sl))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      (⌜err = GoInterface.nil⌝ ∗ isEtcdConnG c conn eps ∗ connTokOk conn P) ∨
        ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
