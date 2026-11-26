/-
`RunDurable(eps, n)` (`examples/etcd/dist/client/durable.go`): the durable workload of `etcd_safe`, on its
orchestrator machine, against every member's client endpoint (`Workload.durable`): `min n 256` puts of
distinct keys `du/k<byte j>` with `v<byte j>`, then one linearizable range of `du/`; a panic unless every
acknowledged put's key is in it with its value at version 1, and every key in it is an attempted put's, with
that put's value at version 1. Lean-first (no Rocq counterpart); #50 N9a (`notes/etcd-dist-plan.md` §23).

**The triple:** from the package's `isPkgInit`, the level token, the endpoints `eps` (read-only) and the
orchestrator's share `durableShare addrs` (global, the start's: the cluster's view `Γ`, auth off, every
endpoint serving a member of it, the prefix `du/` owned in the cluster's shared KV with the owner's half at
`[]`; `KVWorkDefs.lean`), `RunDurable` returns (no panic: the checks hold), the token given back.

**The pure premises:** `n ≥ 0` (`make([]bool, n)` panics otherwise; `deployment.WellFormed` bounds a durable
workload's `Clients` to `[0, MaxDurable]`), and `RunPutGet`'s.
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
abbrev RunDurable.spec : Prop :=
  ∀ [π : NetProtoGS] (eps : GoSlice) (addrs : List GoString) (n : w64),
  0 ≤ sint.Z n →
  Nonempty (WEnv GF) → threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ durableShare (Gg := hG.goose_globalGS) addrs }}
    (App (App (Val (@! client.RunDurable)) (Val #eps)) (Val #n))
  {{ (r : client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
