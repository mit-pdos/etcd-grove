/-
`leases(cli)` (`examples/etcd/leasecatchup/leasecatchup.go`; lease-mono3, 2026-11-06,
`notes/lease-mono3-plan.md`): `cli.Lease.Leases(ctx)` in a context with the examples' request
timeout (`context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`, cancelled after the
call). Lean-first (no Rocq counterpart).

**The triple:** for a client `cli` of the endpoints `eps` (`isNewClient`), a spec `Spec`
registered for `LeaseLeases` at every endpoint and the caller's `Q` that `Spec` gives
(`lessor.Leases`'s premises), from the package's fact: on success (`err = nil`) a
`*LeaseLeasesResponse` whose `Leases` field is a read-only slice of the reply's lease ids, with `Q`
of the reply; otherwise an error. Under the client's context premises, as `grant`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Defs
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
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
abbrev leases.spec : Prop :=
  ∀ [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (eps : List GoString) (V : client.WEnv GF)
    (Spec : GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse)
    (Q : LeaseLeasesRespM → IProp GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup ∗
      isNewClient cl eps V ∗
      isGrpcRpcs eps go!"/etcdserverpb.Lease/LeaseLeases" Spec ∗ □ ▷ Spec () Q }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.leases)) (Val #cl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : LeaseLeasesRespM) (sl : GoSlice),
        structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
        sl ↦*□ (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗ Q m) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end etcd_leasecatchup
end EtcdGrove
end Perennial
