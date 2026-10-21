/-
`(*clientv3.lessor).recvKeepAlive(resp)` (`client/v3/lease.go`; item 1, the client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.recvKeepAlive(resp)` on a lessor (`lessorAt`) with a received keep-alive response
(`keepAliveRespMsg`): under the lock, closes the response's lease's keep-alive if its `TTL` is
not positive, else updates its deadlines and offers the response to each of its channels
(non-blocking); it returns. -/
abbrev lessor.recvKeepAlive.spec : Prop :=
  ∀ (l : Loc) (addr : GoString) (resp : Loc) (m : w64 × w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l [addr] ∗
      keepAliveRespMsg resp m }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"recvKeepAlive")) (Val #resp))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
