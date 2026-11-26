/-
`net.Listen(network, address)` at an address whose net protocols the deployment's start set (etcd-dist N5,
`notes/etcd-dist-plan.md` §19): a member's listener of its peer address, which etcd's peer handler serves across
machines (`PeerServe_dist`, from `httpAddrAt`'s `addrProto`). The listening token is lent by the protocols'
invariant (`listen_au`) and given back at the step, so the address fact stays whole; the listener is open at the
address, with no claim on its requests (`netListenerOpen`). A theorem from the part `Net/`'s `Listen` spec
(`Net/Spec/net/Listen.lean`), `Proof/net/ListenProto.lean`; a third spec of `net.Listen` beside
`Spec/net/Listen.lean`'s (an unreserved address) and `Spec/net/ListenHttp.lean`'s (an address reserved for HTTP).
-/
module

public import Proof.net.InvNet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `net.Listen("tcp", addr)` at an address set to the protocols `P`, `Q` (`addrProto`, persistent) returns `nil`
and a listener open at `addr` (`netListenerOpen`), or a non-nil error. -/
abbrev net.Listen.specProto : Prop :=
  ∀ [HasExt netExt] [NetProtoGS] (network addr : GoString) (P Q : Proto GF),
  {{ ⌜network = go!"tcp"⌝ ∗ addrProto (Gg := hG.goose_globalGS) addr P Q }}
    (App (App (Val (@! net.Listen)) (Val #network)) (Val #addr))
  {{ (l err : GoInterface), RET (PairV #l #err);
      (⌜err = GoInterface.nil⌝ ∗ netListenerOpen l addr) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial

end
