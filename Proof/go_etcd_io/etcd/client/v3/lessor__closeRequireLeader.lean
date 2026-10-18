/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__closeRequireLeader.lean`: a trust-boundary axiom
(item 1, the client lease; `closeRequireLeader` is names only: it reads a context's outgoing
metadata, grpc's `metadata`, which `client/v3`'s translation does not import). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__closeRequireLeader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary** (item 1, the client lease): `closeRequireLeader` takes the lock and, for
each keep-alive in the map, closes the channels whose contexts carry `hasleader` metadata (each
in `ka.chs`, so with its token in the lock invariant), sets them to `nil`, and replaces `chs` and
`ctxs` by fresh slices of the other channels and as many contexts (misaligned:
`issues/etcd-lease-close-require-leader-ctx-misaligned.md`; still contexts of the keep-alive, so
`kaOwn` holds again: equal lengths, each remaining channel's token, each context a context); it
releases the lock and returns. A closed channel leaves `chs`, so it is not closed again. -/
axiom lessor.closeRequireLeader.wp_proof : lessor.closeRequireLeader.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
