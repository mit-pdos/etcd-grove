/-
`writer(cli)` (`examples/k8s/compactor/compactor.go`; K4 of `notes/k8s-compactor-plan.md`): `writes`
puts of `writeKey` with value `strconv.Itoa(i)`, each in a context with the request timeout, a
failed put skipped. Lean-first.

**The triple:** with the client's KV handle (`k8s.clientKvOk`) and the example's invariant
(`cinv`, whose `compact_rev_key` protocol a put of another key keeps), it returns.
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

/-- See the file header. -/
abbrev writer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (γk : KVNames) (γ : CNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor ∗
      clientKvOk cl γk ∗ cinv γk γ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.writer)) (Val #cl))
  {{ RET #(); True }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
