/-
`(*clientv3.lessor).recvKeepAliveLoop()` (`client/v3/lease.go`; item 1, the client lease). Lean-first (no Rocq counterpart).
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

/-- `l.recvKeepAliveLoop()` on a lessor (`lessorAt`) over a connection to `addr` serving the
keep-alive stream, with the right to close `donec` (the `Once`'s resource) and the facts its
error checks need (`eofOk`: `io.EOF` is a client error; `ctxErrClientAll`: a context's `Err()` is):
opens streams (`resetRecv`) and handles their responses (`recvKeepAlive`) until the stop context
is cancelled; then closes `donec` and every keep-alive, under the lock; it returns then (or runs
forever). -/
abbrev lessor.recvKeepAliveLoop.spec : Prop :=
  ∀ (l : Loc) (addr : GoString) (dc : GoChan) (γd : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l addr ∗
      leaseKAStreamOk addr ∗ client.eofOk ∗ client.ctxErrClientAll ∗ ctxErrTargets ∗
      lsF go!"donec" l ↦□ dc ∗ ownBroadcastChan dc γd iprop(True) .Pending }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"recvKeepAliveLoop")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
