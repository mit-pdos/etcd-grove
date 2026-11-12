/-
The trust boundary: the membership buckets of a committed log's image are good for the server's
cluster (D22, J7, 2026-10-26; J0 decision 9). Lean-first (no Rocq counterpart); an axiom: why the
statement is true of the Go code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.clusterImageOk_restModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom membership.clusterImageOk_restModel.wp_proof :
  membership.clusterImageOk_restModel.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
