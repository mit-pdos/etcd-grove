/-
`(*clientv3.lessor).resetRecv()` (`client/v3/lease.go`; item 1, the client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.resetRecv()` on a lessor (`lessorAt`) over a connection to `addr` serving the keep-alive
stream (`leaseKAStreamOk`): a new stream (`LeaseKeepAlive` through the retry lease client, under a
child of the stop context), stored in `l.stream` (the previous one's context cancelled) with its
send end given to a new `sendKeepAliveLoop`; the caller gets the client end with the receive token;
or a client error and a `nil` stream. -/
abbrev lessor.resetRecv.spec : Prop :=
  ∀ (l : Loc) (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l [addr] ∗
      leaseKAStreamOk addr }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"resetRecv")) (Val #()))
  {{ (st err : GoInterface), RET (PairV #st #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames) (Dn : Nat → (w64 × w64) → IProp GF)
          (cd : context.ContextDesc (IProp GF)),
        cliBidiStreamIs st γ pbLeaseKeepAliveRequest pbLeaseKeepAliveResponse
          (fun _ _ => iprop(True)) Dn cd ∗
        cliRecvTok (Rep := pbLeaseKeepAliveResponse) γ []) ∨
      (⌜st = GoInterface.nil⌝ ∗ cliStreamErr err) }}

end spec

end EtcdGrove
end Perennial
