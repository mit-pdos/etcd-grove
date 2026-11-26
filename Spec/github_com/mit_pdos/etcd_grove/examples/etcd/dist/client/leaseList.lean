/-
`leaseList(cli)`: the listing of the leases of `cli`'s member, in a context with the request timeout
(`examples/etcd/dist/client/lease.go`), over the member at another machine. Three triples, one per draft
statement of the call (N2's, `Proof/.../etcd/dist/ClientViewDist.lean`, at the cluster view `Γ`):
- `leaseList.spec` (any lease mode; `Client_LeaseLeases_dist`): the listing names no lease twice;
- `leaseList.specLive` (revocable mode; `Lease_LeasesLive_dist`): the listing is a snapshot of member `mid`'s
  lessor history at an index no earlier than the caller's lower bound;
- `leaseList.specGranted` (monotone mode; `Lease_LeasesGranted_dist`): the listing has every lease the caller
  knows granted at that lessor.
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

/-- `leaseList(cli)` by a client of member `mid` of the view (the caller's `levelTok 0` lent and returned):
`nil` and a listing that names no lease twice, or an error. -/
abbrev leaseList.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ memberCli cl ep V Γ mid }}
    (App (Val (@! client.leaseList)) (Val #cl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗ ⌜ids.Nodup⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- `leaseList(cli)` in revocable lease mode, with a lower bound `n` of member `mid`'s lessor history: `nil`
and the ids of a snapshot of that history at an index `j ≥ n`, or an error. -/
abbrev leaseList.specLive : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64) (n : Nat),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  Γ.kv.lm = .revocable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ memberCli cl ep V Γ mid ∗ lease.lessorLb (Γ.ls mid) n }}
    (App (Val (@! client.leaseList)) (Val #cl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice) (j : Nat),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗
          ⌜n ≤ j⌝ ∗ lease.leaseIdsAt (Γ.ls mid) j ids) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- `leaseList(cli)` in monotone lease mode, for the leases `G` the caller knows granted at member `mid`'s
lessor: `nil` and a listing with no id twice that has every lease of `G`, or an error. -/
abbrev leaseList.specGranted : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64) (G : List w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  Γ.kv.lm = .mono →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ memberCli cl ep V Γ mid ∗
      [∗list] id ∈ G, ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid) i id }}
    (App (Val (@! client.leaseList)) (Val #cl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗
          ⌜ids.Nodup ∧ ∀ id ∈ G, id ∈ ids⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
