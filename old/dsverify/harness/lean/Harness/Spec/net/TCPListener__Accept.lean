/-
`l.Accept()` on a `*TCPListener` (`tcpsock.go`): in the model (`TrustedCode/net.lean`,
`TCPListener.Accept.impl`), the extension's `Accept` on the listener's id. For the listener `lid`
made by `Listen(a)` (`ownListener`) and the protocols of `a` (`addrProto`): on success a fresh
`*TCPConn` as a `net.Conn`, the acceptor's end of a connection dialed to `a` (`ownTCPConn c cid
true`), with its tokens (`connEnd cid true Q P [] []`: write with `Q`, read with `P`) and the
end's fresh token (`connFresh cid true`, exclusive and handed out once: for a server that claims
a per-connection role keyed by `cid`), and no error; on failure (a failure, or the listener closed) `nil` and an `*OpError` of `"accept"`
(`newConnResult`). A call through the `net.Listener` interface holding `l` reduces to this one
(`method_interface_ok`). Proved in `Proof/net/TCPListener__Accept.lean`.
-/
module

public import Harness.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI NetConn

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

/-- See the file header. -/
abbrev net.TCPListener.Accept.spec : Prop :=
  ∀ (l : Loc) (lid : w64) (a : GoString) (P Q : Proto GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownListener (GF := GF) l lid a ∗
      addrProto a P Q }}
    (App (Val (l @!! go.GoType.PointerType net.TCPListener.ty @!! go!"Accept")) (Val #()))
  {{ (cv err : GoInterface), RET (PairV #cv #err);
      net.newConnResult go!"accept" true Q P cv err }}

end spec

end Perennial
