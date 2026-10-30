/-
`c.dialWithBalancer(dopts...)` (`client/v3/client.go`, names only: its body is a trusted unfolding,
`Proof/go_etcd_io/etcd/client/v3/DialWithBalancerBody.lean`; item 5). Lean-first (no Rocq
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

/-- `c.dialWithBalancer()` on a client `New` builds (`retryClientOk`; its configuration `cfg` with
no dial options of the caller's; its token bundle, if any, read-only, with
its tokens `""` or meeting `P` (`tokenBundleInv`); its credentials, read-only;
its endpoints `eps`, read-only, plain, at least one (D27); its resolver, not dialed, with them):
an etcd connection to the servers at `eps` (`isEtcdConnG`: its interceptor's contract once the client
is ready), whose attempts carry no credentials' token or one meeting `P` (`connTokOk`), or an
error. -/
abbrev Client.dialWithBalancer.spec : Prop :=
  ∀ (c : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (cr : GoInterface) (r : Loc)
    (esl : GoSlice) (eps : List GoString) (atb : GoInterface)
    (P : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"cfg" ↦□ cfg ∗
      cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
      clientF c go!"authTokenBundle" ↦□ atb ∗ (⌜atb = GoInterface.nil⌝ ∨ tokenBundleInv atb P) ∗ clientF c go!"creds" ↦□ cr ∗
      clientF c go!"endpoints" ↦□ esl ∗ esl ↦*□ eps ∗ ⌜plainEndpoints eps⌝ ∗
      clientF c go!"resolver" ↦□ r ∗ etcdResolverOwn r eps }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialWithBalancer")) (Val #slice.nil))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      (⌜err = GoInterface.nil⌝ ∗ isEtcdConnG c conn eps ∗ connTokOk conn P) ∨
        ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
