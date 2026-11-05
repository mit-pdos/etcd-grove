/-
`apiserver(cli, shared)` (`examples/k8s/compactor/compactor.go`; K4 and Q1 (c), C3, of
`notes/k8s-compactor-plan.md`): one API server's compactor, its own
(`NewCompactor(cli, interval, clock.RealClock{}, nil)`) or, if `shared`, the process's
(`StartCompactorPerEndpoint(cli, interval)`), then `check` on it. Lean-first.

**The triple:** with `New`'s client of the members `ms` (a refusal-free member, `clientWriteOnce`;
their registrations and start), its KV handle (`clientKvOk`) and watcher handle (`clientWatchOk`: the
compactor's watch loop runs, `ListFromCacheSnapshot` being on by default; Q1 (b)), the claims of its
endpoints for the cluster (`epOf`, at `recorded := True`: the registry's compactor is one of `γk`),
the example's invariant (`cinv`) and the KV invariant of the cluster (`kvInv`, for the read-side
law: a reached revision is at most a read's), `apiserver` returns: no check panics and no compactor
round panics. In compaction mode with etcd's compactor off (`γk.cmp`, `γk.cret = 0`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Inv
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Base
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 k8s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]

variable [sync_sem : sync.Assumptions]

/-- See the file header. -/
abbrev apiserver.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γr : ServerRaftNames)
    (γk : KVNames) (γ : CNames) (shared : Bool),
  (∀ x ∈ ms, kvSame x.γr.kv γk) → γk.cmp = true → γk.cret = 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ([∗list] x ∈ ms, client.srvStart x) ∗ clientKvOk cl γk ∗ clientWatchOk cl γk ∗
      ([∗list] ep ∈ ms.map client.SrvAt.addr, epOf ep γk (fun _ => iprop(True))) ∗ cinv γk γ ∗
      kvInv γr γk }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.apiserver)) (Val #cl))
      (Val #shared))
  {{ RET #(); True }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
