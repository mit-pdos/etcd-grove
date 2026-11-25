/-
`leaseList(cli)`: the listing of the leases of `cli`'s member, in a context with the request timeout
(`examples/etcd/dist/client/lease.go`), over the member at another machine (the draft
`etcd_dist.Client_LeaseLeases_dist`).
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

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `leaseList(cli)` by a client of the member at `ep`, which serves etcd's table: `nil` and a listing that
names no lease twice, or an error. -/
abbrev leaseList.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (γE : GName) (mid : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      isNewClient cl [ep] V ∗ clientNoProxy cl ∗ etcd_dist.etcdAddrAt (Gg := hG.goose_globalGS) ep γE mid }}
    (App (Val (@! client.leaseList)) (Val #cl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗ ⌜ids.Nodup⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
