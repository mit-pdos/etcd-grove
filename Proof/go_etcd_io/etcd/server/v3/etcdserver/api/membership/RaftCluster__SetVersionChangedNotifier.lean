/-
The trust boundary: `(*membership.RaftCluster).SetVersionChangedNotifier(n)`: names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetVersionChangedNotifier

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

axiom membership.RaftCluster.SetVersionChangedNotifier.wp_proof : membership.RaftCluster.SetVersionChangedNotifier.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
