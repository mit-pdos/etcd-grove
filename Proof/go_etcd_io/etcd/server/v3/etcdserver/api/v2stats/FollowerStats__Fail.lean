/-
The trust boundary: `(*v2stats.FollowerStats).Fail()` (names-only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats__Fail

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom v2stats.FollowerStats.Fail.wp_proof : v2stats.FollowerStats.Fail.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
