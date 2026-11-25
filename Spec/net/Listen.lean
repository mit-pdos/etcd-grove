/-
`net.Listen(network, address)` (item 4, the server start): the listener grpc's server is served on, in
the vocabulary of `Proof/net/InvNet.lean`. Since the net swap (etcd-dist D2, 2026-11-22) `net` is the part
`Net/`'s translation over the net extension, and this is a theorem from its `Listen` spec
(`Net/Spec/net/Listen.lean`), `Proof/net/Listen.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `net.Listen("tcp", addr)` with the right to listen at `addr` (`netAddrRsv`, consumed; since
2026-11-25 without the address's pending set, `netAddrPend`, which `http.reserve` takes of a peer address:
`netAddrFree_split`) returns a listener open at `addr` (`netListenerAt`), the address's validity and
listening token (`netAddrLis`; with the pending set, what sets the address's protocols, `netAddrLeft_intro`:
phase 7 S2's interface, 2026-11-24) and `nil`, or a non-nil error. -/
abbrev net.Listen.spec : Prop :=
  ∀ (network addr : GoString),
  {{ ⌜network = go!"tcp"⌝ ∗ netAddrRsv (GF := GF) addr }}
    (App (App (Val (@! net.Listen)) (Val #network)) (Val #addr))
  {{ (l err : GoInterface), RET (PairV #l #err);
      (⌜err = GoInterface.nil⌝ ∗ netListenerAt l addr ∗ netAddrLis addr) ∨
        ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
