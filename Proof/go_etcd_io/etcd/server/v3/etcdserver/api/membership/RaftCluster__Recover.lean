/-
The trust boundary: `(*membership.RaftCluster).Recover(onSet)` (names-only). Lean-first (no Rocq
counterpart); D22 receiver epochs, S8d (2026-10-25, W6), an axiom: why the statement is true of the Go
code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Recover

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

axiom membership.RaftCluster.Recover.wp_proof : membership.RaftCluster.Recover.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
