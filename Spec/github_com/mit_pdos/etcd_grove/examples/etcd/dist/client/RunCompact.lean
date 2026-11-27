/-
`RunCompact(eps)` (`examples/etcd/dist/client/compact.go`): the compact workload of `etcd_safe`, on its
orchestrator machine, against every member's client endpoint (`Workload.compact`): 20 rounds, round `i`
putting `cw/k<i>` with `v`, compacting at the revision before the put's, getting the key (it must read `v` at a
revision at least the put's) and, from the second round, getting the previous successful round's key at its
put's revision (if it succeeds, `v`); a round whose put fails is skipped; then a watch of the last key from
revision 2 (only `v`), and `checkCompactRev`. Lean-first (no Rocq counterpart); #50 F5
(`notes/etcd-dist-plan.md` §26).

**The triple:** from the package's `isPkgInit`, the level token, the endpoints `eps` (read-only) and the
orchestrator's share `compactShare addrs` (global, the start's: the cluster's view `Γ`, auth off, in compaction
mode at retention 1, every endpoint serving a member of it, the KV invariant, the prefix `cw/` owned in the
cluster's shared KV under compact's discipline with the owner's half at `[]`; `CompactWorkDefs.lean`),
`RunCompact` returns (no panic: every check holds), the token given back.

**The pure premises** (each a fact of the deployment or of the logic, as `RunPutGet`'s): a watch environment
(`newClient`'s client), the logic's thread bound (`NewClients`'), the endpoints plain (`clientv3.New`'s:
`WellFormed`'s addresses), `errors.As`'s target `rpctypes.EtcdError` (the request contexts' errors).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CompactWorkDefs
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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev RunCompact.spec : Prop :=
  ∀ [π : NetProtoGS] (eps : GoSlice) (addrs : List GoString),
  Nonempty (WEnv GF) → threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ compactShare (Gg := hG.goose_globalGS) addrs }}
    (App (Val (@! client.RunCompact)) (Val #eps))
  {{ (r : client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
