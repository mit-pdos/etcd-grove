/-
`net.DialTimeout("tcp", a, d)` (`dial.go`): in the model (`TrustedCode/net.lean`,
`DialTimeout.impl`), `Dial`'s model (the timeout is one more reason a dial may fail, which
`Dial`'s spec already allows), so the spec is `Dial`'s, for any duration (the end's tokens and
its fresh token `connFresh cid false` on success). Proved in `Proof/net/DialTimeout.lean`.
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
abbrev net.DialTimeout.spec : Prop :=
  ∀ (a : GoString) (d : w64) (P Q : Proto GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrProto (GF := GF) a P Q }}
    (App (App (App (Val (@! net.DialTimeout)) (Val #(go!"tcp"))) (Val #a)) (Val #d))
  {{ (cv err : GoInterface), RET (PairV #cv #err);
      net.newConnResult go!"dial" false P Q cv err }}

/-- `net.DialTimeout(nw, a, d)` for `nw` `"tcp"` or `"tcp4"` (`net.tcpNet`): as
`net.DialTimeout.spec`. -/
abbrev net.DialTimeoutNet.spec : Prop :=
  ∀ (nw a : GoString) (d : w64) (P Q : Proto GF), net.tcpNet nw →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrProto (GF := GF) a P Q }}
    (App (App (App (Val (@! net.DialTimeout)) (Val #nw)) (Val #a)) (Val #d))
  {{ (cv err : GoInterface), RET (PairV #cv #err);
      net.newConnResult go!"dial" false P Q cv err }}

end spec

end Perennial
