/-
**The lease calls' client fact at the cluster view** (`notes/etcd-dist-plan.md` §18.4; #50, the etcd_safe
lead, 2026-11-25). Lean-first (no Rocq counterpart).

Definitions only. The lease contracts that were drafted here were adopted on 2026-11-26 (F2) as interim
axioms, each in its own Spec/Proof pair: `LeaseGrantDist`, `LeaseGrantLiveDist`, `LeaseLeasesGrantedDist`,
`LeaseLeasesLiveDist` (they read the view's lessor names `Γ.ls mid`: linked only after P-L1, §18.3),
`ClientLeaseLeasesDist`, `ClientLeaseTTLDist` (view-free). The KV calls' contracts are in `KVPutDist.lean`,
`KVGetDist.lean`, `KVDeleteDist.lean`, `KVCompactDist.lean`, `TxnCommitDist.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.InvLease
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace view

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The lease calls (one endpoint: `LeaseLeases` is a member-local read) -/

section lease
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- What every lease draft takes of the client: `New`'s client `cl` of the one endpoint `ep` (no
proxy), its `Lease` field the `*lessor` `lp`, `ep` serving member `mid` of `Γ`. -/
def leaseClientAt [π : NetProtoGS] (cl lp : Loc) (ep : GoString)
    (V : WEnv GF) (Γ : DistView) (mid : w64) : IProp GF :=
  iprop(isNewClient cl [ep] V ∗ clientNoProxy cl ∗
    clientF cl go!"Lease" ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #lp : GoInterface) ∗
    etcdAddrAt (Gg := hG.goose_globalGS) ep Γ mid)

end lease

end view
end etcd_dist
end EtcdGrove
end Perennial
