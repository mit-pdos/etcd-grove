/-
`net.Dial("tcp", a)` for a valid address `a` (`addrOk`, D20; `Dial.impl`,
`Net/TrustedCode/net.lean`): the extension's `Dial` (D8, D16). A failure that leaves nothing gives
the caller's `Qfail`; a new connection `cn` is taken by a logically atomic update over `a`'s pending
set (`netPend`), which gets `cn` (with `netConnAt` and its acceptor's end's fresh resources,
`netFresh cn true`) and then either the dialer's end's fresh resources, the call returning the
dialer's end as a `Conn` (`isConn _ cn false a`) and `Qok cn`, or, abandoned, the dialer's end
closed and its direction shut and empty, the call failing with `Qfail`. A failure's error is
`*OpError{Op: "dial", Source: nil, Addr: x}`, `x` a `*TCPAddr`, whose `Err` is an `*os.SyscallError`
(`resErr`, D14). Proved in `Net/Proof/net/Dial.lean`.

The network `nw` is `"tcp"` or `"tcp4"` (`tcpNet`, D23): the same on the valid IPv4
addresses, the network kept in the connection or listener and put in its errors.

It takes `net`'s package fact (`isPkgInit net`, 2026-11-25, egnet: a `netFD` is net's), which the connection keeps (`fdAt`) for its operations (`Conn.Read`'s
`io.EOF` comparison, the errors' `Error()`: `errnoOk_of_poll`).
-/
module

public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev Dial.spec : Prop :=
  ∀ (nw : GoString), tcpNet nw → ∀ (a : GoString) (Qfail : IProp GF) (Qok : Nat → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ ⌜addrOk a = true⌝ ∗
      (Qfail ∧
        |={⊤,∅}=> ∃ S, netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a S ∗
          ∀ cn, ⌜cn ∉ S⌝ -∗ netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a (S ∪ {[cn]}) -∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
            netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn true -∗
            ((netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ={∅,⊤}=∗ Qok cn) ∧
             (netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false { NetEnd.fresh with closed := true } -∗
              netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ⟨[], .fin⟩ ={∅,⊤}=∗ Qfail))) }}
    (App (App (Val (@! net.Dial)) (Val #nw)) (Val #a))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn, isConn c cn false a ∗ Qok cn) ∨
      (Qfail ∗ ∃ x, netAddr x ∗ resErr (some .sys) go!"dial" interface.nil x none (fun _ => True) err) }}

end spec

end net
end Perennial
