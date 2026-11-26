/-
`RunPutGet(eps)` (`examples/etcd/dist/client/compact.go`): the putget workload of `etcd_safe`, on its
orchestrator machine, against every member's client endpoint (`Workload.putget`): 50 rounds, round `i`
putting `pg/k<i>` with `v<i>` and getting it; a get that returns must return the put's value (else a panic);
a round whose put or get fails is skipped. Lean-first (no Rocq counterpart); #50 N9a
(`notes/etcd-dist-plan.md` §23).

**The triple:** from the package's `isPkgInit`, the level token, the endpoints `eps` (read-only) and the
orchestrator's share `putgetShare addrs` (global, the start's: the cluster's view `Γ`, auth off, every
endpoint serving a member of it, the prefix `pg/` owned in the cluster's shared KV with the owner's half at
`[]`; `KVWorkDefs.lean`), `RunPutGet` returns (no panic: the check holds), the token given back.

**The pure premises** (each a fact of the deployment or of the logic, as `NodeMain`'s): a watch environment
(`newClient`'s client: `Put`/`Get` read none of it), the logic's thread bound (`NewClients`'), the endpoints
plain (`clientv3.New`'s: `WellFormed`'s addresses), `errors.As`'s target `rpctypes.EtcdError` (the request
contexts' errors).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KVWorkDefs
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
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev RunPutGet.spec : Prop :=
  ∀ [π : NetProtoGS] (eps : GoSlice) (addrs : List GoString),
  Nonempty (WEnv GF) → threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ putgetShare (Gg := hG.goose_globalGS) addrs }}
    (App (Val (@! client.RunPutGet)) (Val #eps))
  {{ (r : client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
