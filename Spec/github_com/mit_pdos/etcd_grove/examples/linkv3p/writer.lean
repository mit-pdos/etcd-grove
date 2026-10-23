/-
`writer(clis, w, tried, lo, hi)` (`examples/linkv3p/linkv3p.go`; W4d of
`notes/watch-cut-plan.md`, 2026-10-22; watchkv's `writer` with a client picked at random per put).
Lean-first (no Rocq counterpart).

**The triple:** from the package facts, the clients `clis` (not empty), each `New`'s client of
the members `ms` at the bridges, writing at most once (D29), each member's `memberPut` at the
history's names `γr` (watchkv's workload `P` of the puts tried), `tried` read-only, the client's
`etcdKV` in an invariant (`wkKV`) and the writers' log's lock (`wsInvH`), `writer` does the puts
`tried[lo:hi]` and returns; each that returned no error is in the log with its `okFactH`.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev writer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (clis : GoSlice) (cls : List Loc)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γr : ReadNames) (w : Loc)
    (tsl : GoSlice) (tried : List wkv) (lo hi : w64) (P : List (GoString × GoString)),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  γr.kv.wl = watchkv.workload P → tried.map pairOf = P → receiptBound GF ≤ 2 ^ 62 →
  cls ≠ [] → 0 ≤ sint.Z lo → sint.Z lo ≤ sint.Z hi → sint.Z hi ≤ tried.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      clis ↦*□ cls ∗
      ([∗list] cl ∈ cls, isNewClient cl (ms.map client.SrvAt.addr) V ∗
        client.clientWriteOnce cl (ms.map client.SrvAt.addr)) ∗
      ([∗list] x ∈ ms, memberPut γr x) ∗
      tsl ↦*□ tried ∗ watchkv.wkKV γr ∗
      sync.isMutex (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" w)
        (wsInvH w γr) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.writer))
      (Val #clis)) (Val #w)) (Val #tsl)) (Val #lo)) (Val #hi))
  {{ RET #(); True }}

end spec

end linkv3p
end EtcdGrove
end Perennial
