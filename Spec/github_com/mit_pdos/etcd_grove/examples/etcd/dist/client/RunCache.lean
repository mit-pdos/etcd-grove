/- Lean-first (no Rocq counterpart).

`RunCache(eps, nodes, nops, ready)` (`examples/etcd/dist/client/watch.go`): **the cache workload of
`etcd_safe`, on its orchestrator machine** (#50 F6, `notes/etcd-dist-plan.md` §29): the cache example's
`Main` (`Spec/.../cache/Main.lean`) without its start, its writers at machines of their own. The writers'
Puts picked (`GenAll`, `len(nodes) * nops` under `ck/`); a client of every member's endpoint (`newClient`);
etcd's watch cache of `ck/` over it (`cache.New`, the default configuration) and `defer c.Close()`; the
cache's watch of `ck/` from revision `2` (`c.Watch`, `WithPrefix`, `WithRev(2)`); `ready()`; the writers at
their machines (`remoteWriters`); the watch read until it has reported every successful Put
(`cacheCollect`, with a timer cancelling the watch after `readTimeout`); a progress notification
requested (`c.RequestProgress`) and awaited (`awaitProgress`), then checked (`checkProgress`: not past the
last event); the events checked against the writes (`etcdstart.Check`: exactly the writes, gap-free from
revision `2`); and, if a Put succeeded, the cache's `Get` of `ck/` at the highest successful Put's revision
(`WithPrefix`, `WithRev(r)`, under a timeout) and its check (`checkGet`: each key's last watched value at or
below `r`, and every watched key). A failed connection, `cache.New`'s error, a watch that ended first and
the `Get`'s error end the workload without a check.

**The triple:** from the package's `isPkgInit`, the machine's thread token (whole: `Cache.Watch` takes it,
where the other workloads take its level-`0` part, `threadTok_level0`), the endpoints `eps`
and the writer machines' addresses `nodes` (read-only), a `ready` safe to call, and the orchestrator's
share `cacheShare addrs ns` (global, the start's: the watch workload's, `CacheWorkDefs.lean`: the
cluster's view, every endpoint serving a member of it, the cluster's client half at the boot's state,
the writer machines' share), `RunCache` returns (no panic: every check holds), the token given back (`defer c.Close()` ran: the cache's
goroutines are stopped).

**The pure premises** (facts of the deployment or of the logic): `RunWatch.spec`'s (a watch environment,
the logic's thread bound, plain endpoints, the writers' count fits, the logic's receipt bound `receiptBound
GF ≤ 2 ^ 56`, so that the writers' Puts, fewer than the receipts (`GenAll_receipts.spec`), fit their wire:
N10a2 §24.7), and that `errors.As` can take `*rpctypes.EtcdError` (`RunPutGet.spec`'s: the cache's gets take
any context, whose errors are then client errors, `ctxErrClientAllW_of`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CacheWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open etcd_dist etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev RunCache.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] (eps nodes : GoSlice) (addrs ns : List GoString) (nops : w64) (ready : GoFunc),
  Nonempty (WEnv GF) → threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs →
  0 ≤ sint.Z nops → ns.length * sint.Z nops < 2 ^ 63 → receiptBound GF ≤ 2 ^ 56 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      threadTok ∗ eps ↦*□ addrs ∗ nodes ↦*□ ns ∗
      ({{ True }} (App (Val #ready) (Val #())) {{ RET #(); True }}) ∗
      cacheShare (Gg := hG.goose_globalGS) addrs ns }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunCache))
      (Val #eps)) (Val #nodes)) (Val #nops)) (Val #ready))
  {{ (r : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Result), RET #r; threadTok }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
