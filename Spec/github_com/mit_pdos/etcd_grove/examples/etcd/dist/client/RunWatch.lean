/- Lean-first (no Rocq counterpart).

`RunWatch(eps, nodes, nops, ready)` (`examples/etcd/dist/client/watch.go`): **the watch workload of
`etcd_safe`, on its orchestrator machine** (#50 N10a, `notes/etcd-dist-plan.md` §24): the writers' Puts
picked (`GenAll`, `len(nodes) * nops` under `wk/`); a client of every member's endpoint (`newClient`)
and its watch of `wk/` from revision `1` (`WithPrefix`, `WithRev(1)`, `WithProgressNotify`,
`WithCreatedNotify`), kept across faults (the client reopens its stream at a reachable member and
resumes it); `ready()`; the writers at their machines (`remoteWriters`); the watch read until it has
reported every successful Put (`etcdstart.Collect`, with a timer cancelling the watch after
`readTimeout`) and checked against the writes (`etcdstart.Check`: exactly the writes, gap-free from
revision `2`). A failed connection or a watch that ended first ends the workload without a check.

**The triple:** from the package's `isPkgInit`, the level token (the machine's), the endpoints `eps`
and the writer machines' addresses `nodes` (read-only), a `ready` safe to call, and the orchestrator's
share `watchShare WS addrs ns` (global, the start's: the cluster's view, every endpoint serving a
member of it, the cluster's client half at the boot's state, the writer machines' share `WS`;
`WatchWorkDefs.lean`), `RunWatch` returns (no panic: the check holds), the token given back. `WS` is
the parameter of `remoteWriters.specWith`, which the proof takes as a hypothesis.

**The pure premises** (facts of the deployment or of the logic): a watch environment (`newClient`'s
client; the watch contract reads none of it), the logic's thread bound and plain endpoints
(`newClient`'s), and the writers' count fits (`0 ≤ nops`, `len(nodes) * nops < 2 ^ 63`: `WellFormed`'s
bounds).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open etcd_dist etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev RunWatch.spec (WS : DistView → List GoString → IProp GF) : Prop :=
  ∀ [π : NetProtoGS] (eps nodes : GoSlice) (addrs ns : List GoString) (nops : w64) (ready : GoFunc),
  Nonempty (WEnv GF) → threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs →
  0 ≤ sint.Z nops → ns.length * sint.Z nops < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ nodes ↦*□ ns ∗
      ({{ True }} (App (Val #ready) (Val #())) {{ RET #(); True }}) ∗
      watchShare (Gg := hG.goose_globalGS) WS addrs ns }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunWatch))
      (Val #eps)) (Val #nodes)) (Val #nops)) (Val #ready))
  {{ (r : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
