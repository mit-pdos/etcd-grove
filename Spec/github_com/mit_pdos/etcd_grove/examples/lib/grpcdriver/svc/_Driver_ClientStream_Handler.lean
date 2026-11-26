/- Lean-first (no Rocq counterpart).

`svc._Driver_ClientStream_Handler(srv, stream)` (`svc/svc.go`, the generated stream handler of the driver's
`ClientStream`), as etcd's `_Watch_Watch_Handler`: for a service value `srv` whose type implements
`DriverServer` and whose `ClientStream` meets its contract with `S` (`strmMethodOk`, on the wrapped end with
its `SendAndClose`), on a raw server end `stream` of a fresh stream (`srvRawStreamIsW`, both tokens at
`[]`) of `StringValue`s (`strmT`) with the specification at the run's incoming metadata and `S`: wraps
the stream and runs `srv.ClientStream` on it; returns its error (`srvErrOk`) and `S`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.StreamDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove google_golang_org.protobuf.types.known

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- See the file header. -/
abbrev _Driver_ClientStream_Handler.spec : Prop :=
  ∀ (Up : Nat → (strmT (GF := GF)).M → IProp GF) (Spec : GrpcMd → StreamSpec (strmT (GF := GF)))
    (srv : GoInterfaceOk) (S : IProp GF) (γ : StreamNames) (Dn : Nat → (strmT (GF := GF)).M → IProp GF)
    (ci : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (st : GoInterface),
  go.typeSetContains srv.ty DriverServer.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ∗
      strmMethodOk (Req := strmT) (Rep := strmT) #(methods srv.ty go!"ClientStream" srv.v) S Up Spec ∗
      grpcStreamSpecAt Spec ci γ Dn ∗ S ∗ srvRawStreamIsW st γ strmT strmT Up Dn ci cd ∗
      srvRecvTok (Req := strmT (GF := GF)) γ [] ∗ srvSendTok (Rep := strmT (GF := GF)) γ [] }}
    (streamHandlerCall (@! _Driver_ClientStream_Handler) #(GoInterface.ok srv) #st)
  {{ (err : GoInterface), RET #err; go_etcd_io.etcd.cache.v3.srvErrOk err ∗ S }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
