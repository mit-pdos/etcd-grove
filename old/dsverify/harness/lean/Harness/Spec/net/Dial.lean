/-
`net.Dial("tcp", a)` (`dial.go`): in the model (`TrustedCode/net.lean`, `Dial.impl`), the
extension's `Dial` (a network other than `"tcp"` is stuck). Knowing the protocols `P` (what
dialers write) and `Q` (what acceptors write) of the configured address `a` (`addrProto`,
persistent): on success a fresh `*TCPConn` as a `net.Conn`, which is the dialer's end of a new
connection `cid` (`ownTCPConn c cid false`, persistent), with its tokens (`connEnd cid false P Q
[] []`: write with `P`, read with `Q`) and the end's fresh token (`connFresh cid false`,
exclusive and handed out once: for a client that registers per-connection ghost state keyed by
`cid`), and no error; on failure `nil` and an `*OpError` of `"dial"` (`newConnResult`). Proved in
`Proof/net/Dial.lean`.
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
abbrev net.Dial.spec : Prop :=
  ∀ (a : GoString) (P Q : Proto GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrProto (GF := GF) a P Q }}
    (App (App (Val (@! net.Dial)) (Val #(go!"tcp"))) (Val #a))
  {{ (cv err : GoInterface), RET (PairV #cv #err);
      net.newConnResult go!"dial" false P Q cv err }}

/-- `net.Dial(nw, a)` for `nw` `"tcp"` or `"tcp4"` (`net.tcpNet`; the model treats `"tcp4"` as
`"tcp"`, `TrustedCode/net.lean`): as `net.Dial.spec`. -/
abbrev net.DialNet.spec : Prop :=
  ∀ (nw a : GoString) (P Q : Proto GF), net.tcpNet nw →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrProto (GF := GF) a P Q }}
    (App (App (Val (@! net.Dial)) (Val #nw)) (Val #a))
  {{ (cv err : GoInterface), RET (PairV #cv #err);
      net.newConnResult go!"dial" false P Q cv err }}

end spec

end Perennial
