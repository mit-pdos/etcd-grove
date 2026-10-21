/-
`(*clientv3.lessor).KeepAlive(ctx, id)` (`client/v3/lease.go`; item 1, the client lease). Lean-first (no Rocq counterpart).
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

/-- `l.KeepAlive(ctx, id)` on a lessor (`lessorAt`) over a connection to `addr` serving the
keep-alive stream (with the facts the receive loop's error checks need), for a context: a new
channel the caller may receive from (`isChanAny`; the lessor keeps its close token), added to the
lease `id`'s keep-alive (a new one if there is none), with a goroutine closing it once `ctx` is done
and, the first time, the receive and deadline loops; or, if the receive loop has stopped, a closed
channel and an `ErrKeepAliveHalted` error. -/
abbrev lessor.KeepAlive.spec : Prop :=
  ∀ (l : Loc) (addr : GoString) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l [addr] ∗
      leaseKAStreamOk addr ∗ client.eofOk ∗ client.ctxErrClientAll ∗ ctxErrTargets ∗ context.isContext ctx cd }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"KeepAlive")) (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (ch : Loc) (err : GoInterface), RET (PairV #ch #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ ∃ γ : ChanNames, isChanAny γ ch) }}

end spec

end EtcdGrove
end Perennial
