/-
`ready(cli)` (`examples/k8s/compactor/compactor.go`; K4 of `notes/k8s-compactor-plan.md`): a latest
`Get` of `compact_rev_key` within the request timeout, reporting whether it succeeded. Lean-first.

**The triple:** with `New`'s client of the members `ms` (their registrations and start), it returns
some `bool`.
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
abbrev ready.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ([∗list] x ∈ ms, client.srvStart x) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ready)) (Val #cl))
  {{ (b : Bool), RET #b; True }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
