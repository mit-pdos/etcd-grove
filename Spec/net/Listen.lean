/-
`net.Listen(network, address)` (names only; item 4, the server start): the listener grpc's server is
served on. The vocabulary: `Proof/net/InvNet.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `net.Listen("tcp", addr)` on a free address (`netAddrFree`, consumed) returns a listener bound
at `addr` (`netListenerAt`) and `nil`, or a non-nil error. -/
abbrev net.Listen.spec : Prop :=
  ∀ (network addr : GoString),
  {{ ⌜network = go!"tcp"⌝ ∗ netAddrFree (GF := GF) addr }}
    (App (App (Val (@! net.Listen)) (Val #network)) (Val #addr))
  {{ (l err : GoInterface), RET (PairV #l #err);
      (⌜err = GoInterface.nil⌝ ∗ netListenerAt l addr) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
