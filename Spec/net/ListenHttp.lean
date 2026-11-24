/-
`net.Listen(network, address)` at an address reserved for HTTP (2026-11-24, `notes/decisions.md`, "`http.reserve`
fixes the address's net protocols"): a member's listener of its peer address, which net/http serves
(`http.register`). The address's net protocols were set to net/http's when its HTTP protocol was reserved
(`http.httpAddrFree_set`, `Proof/net/http/AddrNet.lean`), so the listener is made from the right to listen at it
reserved for HTTP (`http.httpAddrFree`) and leaves nothing that sets the address's protocols (no `netAddrLeft`). A
theorem from the part `Net/`'s `Listen` spec (`Net/Spec/net/Listen.lean`), `Proof/net/ListenHttp.lean`; the second
spec of `net.Listen` beside `Spec/net/Listen.lean`'s (an unreserved address).
-/
module

public import Proof.net.http.AddrNet

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

/-- `net.Listen("tcp", addr)` with the right to listen at `addr`, reserved for HTTP (`http.httpAddrFree`, consumed)
returns `nil` and a listener at `addr` (`netListenerAt`: the Go `*TCPListener` `l` tied to the extension's listener
open at `addr`, with the claim on `addr`'s requests), or a non-nil error. -/
abbrev net.Listen.specHttp : Prop :=
  ∀ (network addr : GoString),
  {{ ⌜network = go!"tcp"⌝ ∗ http.httpAddrFree (GF := GF) addr }}
    (App (App (Val (@! net.Listen)) (Val #network)) (Val #addr))
  {{ (l err : GoInterface), RET (PairV #l #err);
      (⌜err = GoInterface.nil⌝ ∗ netListenerAt l addr) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
