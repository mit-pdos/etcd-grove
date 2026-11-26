/-
`leaseGrant(cli, ttl)`: a lease of TTL `ttl` granted through `cli`, in a context with the request timeout
(`examples/etcd/dist/client/lease.go`), at the member at another machine. Two triples, one per lease mode,
over the drafts (N2's, `Proof/.../etcd/dist/ClientViewDist.lean`, at the cluster view `Γ`):
- `leaseGrant.spec` (revocable mode; `Lease_GrantLive_dist`): the reply's lease is live in member `mid`'s
  lessor history from an index (leaseexpiryN's grant);
- `leaseGrant.specMono` (monotone mode; `Lease_Grant_dist`): the reply's lease is granted at that lessor
  (leasecatchup's grant).
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist.view

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `leaseGrant(cli, ttl)` in revocable lease mode, by a client of member `mid` of the view: `nil` and the
reply, whose lease (non-zero) is live in member `mid`'s lessor history from an index, with its request's
TTL; or an error and `null`. -/
abbrev leaseGrant.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64) (ttl : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  Γ.kv.lm = .revocable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ memberCli cl ep V Γ mid }}
    (App (App (Val (@! client.leaseGrant)) (Val #cl)) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ ∃ (i : Nat) (l : Loc),
          lease.leaseLiveFrom (Γ.ls mid) i m.id l ∗ lease.leaseReqIs (Γ.ls mid) m.id ttl) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- `leaseGrant(cli, ttl)` in monotone lease mode: `nil` and the reply, whose lease (non-zero) is granted at
member `mid`'s lessor; or an error and `null`. -/
abbrev leaseGrant.specMono : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64) (ttl : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  Γ.kv.lm = .mono →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ memberCli cl ep V Γ mid }}
    (App (App (Val (@! client.leaseGrant)) (Val #cl)) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid) i m.id) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
