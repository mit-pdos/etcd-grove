/-
`grant(cli)` (`examples/etcd/leasecatchup/leasecatchup.go`; lease-mono3, 2026-11-06,
`notes/lease-mono3-plan.md`): `cli.Lease.Grant(ctx, grantTTL)` in a context with the examples'
request timeout (`context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`, cancelled
after the call). Lean-first (no Rocq counterpart).

**The triple:** for a client `cli` of the endpoints `eps` (`isNewClient`, `NewClients`'s), a spec
`Spec` registered for `LeaseGrant` at every endpoint and the caller's `Q` that `Spec` gives of the
request `(grantTTL, 0)` (`lessor.Grant`'s premises), from the package's fact: on success (`err =
nil`) a `*LeaseGrantResponse` whose `ID` field is the reply's lease id, read-only, with `Q` of the
reply; otherwise an error. Under the client's context premises (`ContextReadErrs`,
`ContextErrsClient`, `errors.As`'s target), as `lessor.Grant`'s callers'.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Defs
public import Spec.go_etcd_io.etcd.client.v3.lessor__Grant
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- See the file header. -/
abbrev grant.spec : Prop :=
  ∀ [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (eps : List GoString) (V : client.WEnv GF)
    (Spec : GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse)
    (Q : LeaseGrantRespM → IProp GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup ∗
      isNewClient cl eps V ∗
      isGrpcRpcs eps go!"/etcdserverpb.Lease/LeaseGrant" Spec ∗ □ ▷ Spec (grantTTL, W64 0) Q }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.grant)) (Val #cl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗ Q m) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end etcd_leasecatchup
end EtcdGrove
end Perennial
