/-
`writer(clis, w, tried, lo, hi)` (`examples/linkv3p/linkv3p.go`; W4d of
`notes/watch-cut-plan.md`, 2026-10-22; watchkv's `writer` with a client picked at random per put).
Lean-first (no Rocq counterpart).

**The triple:** from the package facts, the clients `clis` (not empty), each `New`'s client of
the members `ms` at the bridges, writing at most once (D29), each member's `memberPut` at the
cluster's KV `γ.kv`, `tried` read-only, the clients' adapter's invariant (`kmInv γ`) whose
application property is the plan's (`γ.W = wkW P`, `P` the puts tried; D45/D48, 2026-10-26: until
then the client's `etcdKV` in watchkv's `wkKV`, at watchkv's server workload) and the writers'
log's lock (`wsInvH`), `writer` does the puts `tried[lo:hi]` and returns; each that returned no
error is in the log with its `okFactK`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchWrites
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.linkv3p

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev writer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (clis : GoSlice) (cls : List Loc)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γ : client.KMNames) (w : Loc)
    (tsl : GoSlice) (tried : List wkv) (lo hi : w64) (P : List (GoString × GoString)),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  γ.W = wkW P → tried.map pairOf = P →
  cls ≠ [] → 0 ≤ sint.Z lo → sint.Z lo ≤ sint.Z hi → sint.Z hi ≤ tried.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      clis ↦*□ cls ∗
      ([∗list] cl ∈ cls, isNewClient cl (ms.map client.SrvAt.addr) V ∗
        client.clientWriteOnce cl (ms.map client.SrvAt.addr)) ∗
      ([∗list] x ∈ ms, memberPut γ.kv x) ∗
      tsl ↦*□ tried ∗ client.kmInv γ ∗
      sync.isMutex (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" w)
        (wsInvH w γ) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.writer))
      (Val #clis)) (Val #w)) (Val #tsl)) (Val #lo)) (Val #hi))
  {{ RET #(); True }}

end spec

end linkv3p
end EtcdGrove
end Perennial
