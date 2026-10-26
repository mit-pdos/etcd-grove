/-
The trust boundary: `(*lease.lessor).Recover(b, rd)` (names-only). Lean-first (no Rocq
counterpart); D22 receiver epochs, S8c (2026-10-24), an axiom: why the statement is true of the Go
code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover

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

axiom lease.lessor.Recover.wp_proof : lease.lessor.Recover.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
