/-
`net.Listen("tcp", a)` (`dial.go`): in the model (`TrustedCode/net.lean`, `Listen.impl`), the
extension's `Listen` (a network other than `"tcp"` is stuck, so the spec is stated for `"tcp"`).
With the token of the configured address `a` (`addrTok`): on success a fresh `*TCPListener` as a
`net.Listener`, which is the extension's listener `lid` on `a` (`ownListener`, persistent), and
no error; on failure `nil` and an `*OpError` of `"listen"` (`opErr`). The token comes back in
both cases (on success it is what keeps another `Listen(a)` from succeeding:
`NetConn.listening`). Proved in `Proof/net/Listen.lean`.

`net.ListenWild.spec`: `net.Listen("tcp", h ++ ":" ++ port)` on a wildcard host `h` (`":port"`,
`"0.0.0.0:port"`, `"[::]:port"`: `NetConn.wildcardHosts`) at the node whose IP is `ip`
(`nodeIp ip`, which the statement gives each node for its configured IP): as `net.Listen.spec`
for the node's own address `ip ++ ":" ++ port`, with that address's token.
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
abbrev net.Listen.spec : Prop :=
  ∀ (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrTok (GF := GF) a }}
    (App (App (Val (@! net.Listen)) (Val #(go!"tcp"))) (Val #a))
  {{ (lv err : GoInterface), RET (PairV #lv #err); addrTok a ∗
      ((∃ (l : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
            err = interface.nil⌝ ∗ net.ownListener l lid a) ∨
       (∃ i, ⌜lv = interface.nil ∧ err = interface.ok i⌝ ∗
          ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code err)) }}

/-- See the file header. -/
abbrev net.ListenWild.spec : Prop :=
  ∀ (ip h port : GoString), h ∈ wildcardHosts →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ nodeIp (GF := GF) ip ∗
      addrTok (GF := GF) (ip ++ go!":" ++ port) }}
    (App (App (Val (@! net.Listen)) (Val #(go!"tcp"))) (Val #(h ++ go!":" ++ port)))
  {{ (lv err : GoInterface), RET (PairV #lv #err); addrTok (ip ++ go!":" ++ port) ∗
      ((∃ (l : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
            err = interface.nil⌝ ∗ net.ownListener l lid (ip ++ go!":" ++ port)) ∨
       (∃ i, ⌜lv = interface.nil ∧ err = interface.ok i⌝ ∗
          ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code err)) }}

/-- `net.Listen(nw, a)` for `nw` `"tcp"` or `"tcp4"` (`net.tcpNet`; the model treats `"tcp4"`
as `"tcp"`, `TrustedCode/net.lean`): as `net.Listen.spec`. -/
abbrev net.ListenNet.spec : Prop :=
  ∀ (nw a : GoString), net.tcpNet nw →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrTok (GF := GF) a }}
    (App (App (Val (@! net.Listen)) (Val #nw)) (Val #a))
  {{ (lv err : GoInterface), RET (PairV #lv #err); addrTok a ∗
      ((∃ (l : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
            err = interface.nil⌝ ∗ net.ownListener l lid a) ∨
       (∃ i, ⌜lv = interface.nil ∧ err = interface.ok i⌝ ∗
          ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code err)) }}

/-- `net.Listen(nw, h ++ ":" ++ port)` on a wildcard host, for `nw` `"tcp"` or `"tcp4"`: as
`net.ListenWild.spec`. -/
abbrev net.ListenWildNet.spec : Prop :=
  ∀ (nw ip h port : GoString), net.tcpNet nw → h ∈ wildcardHosts →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ nodeIp (GF := GF) ip ∗
      addrTok (GF := GF) (ip ++ go!":" ++ port) }}
    (App (App (Val (@! net.Listen)) (Val #nw)) (Val #(h ++ go!":" ++ port)))
  {{ (lv err : GoInterface), RET (PairV #lv #err); addrTok (ip ++ go!":" ++ port) ∗
      ((∃ (l : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
            err = interface.nil⌝ ∗ net.ownListener l lid (ip ++ go!":" ++ port)) ∨
       (∃ i, ⌜lv = interface.nil ∧ err = interface.ok i⌝ ∗
          ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code err)) }}

end spec

end Perennial
