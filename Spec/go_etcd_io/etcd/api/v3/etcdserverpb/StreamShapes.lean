/-
# The server-streaming stubs' and handlers' shapes (WP forms; verify round, A6 completeness F1)

`KV.RangeStream` and `Maintenance.Snapshot` are server-streaming: the generated stub opens the
stream, sends the one request and closes its half; the generated handler receives the one request,
then calls the service's method on it and a wrapper of the stream. Their message types have no
translated Lean type (names only), so the generic wrappers are grpc's `genCliAt`/`genSrvAt` (whose
intended realization is the wrapper's persisted points-to), not a typed points-to as for the
watch and keep-alive streams (`streamStubWP`, `_Lease_LeaseKeepAlive_Handler.spec`).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI
open go_etcd_io.etcd.api.v3

section shapes
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **What a server-streaming stub's caller must establish** (WP form): with the call options
(grpc's `StaticMethod()`, then the caller's), the connection's `NewStream` of the stream descriptor
`sd` and method `m`; on success, with the wrapper `x` over the stream (`genCliAt`), the stream's
`SendMsg` of the request `q` and then its `CloseSend`; the stub returns the wrapper (as the stream
interface) when all three succeed, a `nil` stream with the first error otherwise. -/
def serverStreamStubWP (cc : GoInterface) (sd : Loc) (m : val) (reqT repT : go.GoType)
    (ctx : GoInterface) (q : Loc) (os : List GoInterface) (Ψ : val → IProp GF) : IProp GF :=
  iprop(∀ (cOpts : GoSlice) (sm : GoInterface),
    Grpc.callOptOk sm -∗ cOpts ↦* (sm :: os) -∗
    WP (App (App (App (App (Val (cc @!! google_golang_org.grpc.ClientConnInterface.ty @!! go!"NewStream"))
        (Val #ctx)) (Val #sd)) (Val m)) (Val #cOpts))
      {{ v, ∃ (st err : GoInterface), ⌜v = PairV #st #err⌝ ∗
          ((⌜err ≠ GoInterface.nil⌝ -∗ Ψ (PairV #GoInterface.nil #err)) ∧
           (⌜err = GoInterface.nil⌝ -∗ ∀ x : Loc, Grpc.genCliAt x st reqT repT -∗
              WP (App (Val (st @!! google_golang_org.grpc.ClientStream.ty @!! go!"SendMsg"))
                  (Val #(Proto.msgVal reqT q)))
                {{ v1, ∃ e1 : GoInterface, ⌜v1 = #e1⌝ ∗
                    ((⌜e1 ≠ GoInterface.nil⌝ -∗ Ψ (PairV #GoInterface.nil #e1)) ∧
                     (⌜e1 = GoInterface.nil⌝ -∗
                        WP (App (Val (st @!! google_golang_org.grpc.ClientStream.ty @!! go!"CloseSend")) (Val #()))
                          {{ v2, ∃ e2 : GoInterface, ⌜v2 = #e2⌝ ∗
                              ((⌜e2 ≠ GoInterface.nil⌝ -∗ Ψ (PairV #GoInterface.nil #e2)) ∧
                               (⌜e2 = GoInterface.nil⌝ -∗
                                  Ψ (PairV #(interface.mkOk (go.GoType.PointerType
                                    (google_golang_org.grpc.GenericClientStream.ty reqT repT)) #x)
                                    #GoInterface.nil))) }})) }})) }})

/-- **A server-streaming handler's body** (WP form): with a fresh request holder `m` of type
`*reqT` (some content), the stream's `RecvMsg` into it; its error returned, else the service's
method `meth` of `srv` on `m` and the wrapper `x` over the stream (`genSrvAt`), whose result the
handler returns. -/
def serverStreamHandlerWP (srv : GoInterfaceOk) (meth : GoString) (reqT repT : go.GoType)
    (st : GoInterface) (Ψ : val → IProp GF) : IProp GF :=
  iprop(∀ (m : Loc) (c0 : Proto.Content), Proto.msgAt reqT m (DFrac.own 1) c0 -∗
    WP (App (Val (st @!! google_golang_org.grpc.ServerStream.ty @!! go!"RecvMsg")) (Val #(Proto.msgVal reqT m)))
      {{ v, ∃ err : GoInterface, ⌜v = #err⌝ ∗
          ((⌜err ≠ GoInterface.nil⌝ -∗ Ψ #err) ∧
           (⌜err = GoInterface.nil⌝ -∗ ∀ x : Loc, Grpc.genSrvAt x st reqT repT -∗
              WP (App (App (Val #(methods srv.ty meth srv.v)) (Val #m))
                (Val #(interface.mkOk (go.GoType.PointerType
                  (google_golang_org.grpc.GenericServerStream.ty reqT repT)) #x))) {{ Ψ }})) }})

end shapes

end EtcdServerPb
end EtcdGrove
end Perennial
