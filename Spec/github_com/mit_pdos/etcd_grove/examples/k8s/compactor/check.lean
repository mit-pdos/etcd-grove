/-
`check(cli, c)` (`examples/k8s/compactor/compactor.go`; Q1 (c), C3, of `notes/k8s-compactor-plan.md`):
an API server's checks of its compactor `c` (an interface value of the local `compactorAPI`, holding
etcd3's `*compactor`): its `CompactRevision` sampled `samples` times an interval apart, `Stop`, then
a latest `Get` of `compact_rev_key` and the checks, each a `panic` if it fails: the samples never
decrease, the last is at most the `Get`'s header revision, and the key, if present, parses to a
revision at most a second `Get`'s. Lean-first.

**The triple:** with a compactor of the cluster `γk` (`isCompactor`, of any client `cl'`: a shared
compactor's client may be another API server's) at the lower bound `0`, `New`'s client `cl` of the
members `ms` (refusal-free, `clientWriteOnce`; their registrations and start) and its KV handle
(`clientKvOk`), the example's invariant (`cinv`) and the KV invariant of the cluster (`kvInv`, for
the read-side law: a reached revision is at most a read's), `check` returns: no check panics.
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
abbrev check.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γr : ServerRaftNames)
    (γk : KVNames) (γ : CNames) (c cl' : Loc) (γc : CompactorNames),
  (∀ x ∈ ms, kvSame x.γr.kv γk) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ([∗list] x ∈ ms, client.srvStart x) ∗ clientKvOk cl γk ∗ cinv γk γ ∗ kvInv γr γk ∗
      isCompactor c cl' γk (fun _ => iprop(True)) γc ∗ compactRevLb γc (W64 0) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.check)) (Val #cl))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.compactor.ty)
        #c : GoInterface)))
  {{ RET #(); True }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
