-- The copy for the part `KvRaft/` of `Net/Spec/net/DialTimeout.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`net.DialTimeout("tcp", a, timeout)` for a valid address `a` (`addrOk`, D20; `DialTimeout.impl`,
`Net/TrustedCode/net.lean`, D19): as `net.Dial` (`Dial.spec`: the extension's `Dial`, D8, D16),
but a failure's `Err` is an `*os.SyscallError` or a timeout, `net`'s `errTimeout` (`et`) or
`poll.ErrDeadlineExceeded`'s value (`ed`): both occur (`TestDialTimeoutAccepted`). The timeout's
value is not modeled. Proved in `Net/Proof/net/DialTimeout.lean`.

The network `nw` is `"tcp"` or `"tcp4"` (`tcpNet`, D23): the same on the valid IPv4
addresses, the network kept in the connection or listener and put in its errors.

It takes `net`'s package fact (`isPkgInit net`, 2026-11-25, egnet: a `netFD` is net's), which the connection keeps (`fdAt`) for its operations (`Conn.Read`'s
`io.EOF` comparison, the errors' `Error()`: `errnoOk_of_poll`).
-/
module

public import KvRaft.Proof.net.Base

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
abbrev DialTimeout.spec : Prop :=
  ∀ (nw : GoString), tcpNet nw → ∀ (a : GoString) (dur : w64) (et ed : GoInterface) (Qfail : IProp GF) (Qok : Nat → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ ⌜addrOk a = true⌝ ∗
      globalAddr errTimeout ↦□ et ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      (Qfail ∧
        |={⊤,∅}=> ∃ S, netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a S ∗
          ∀ cn, ⌜cn ∉ S⌝ -∗ netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a (S ∪ {[cn]}) -∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
            netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn true -∗
            ((netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ={∅,⊤}=∗ Qok cn) ∧
             (netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false { NetEnd.fresh with closed := true } -∗
              netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ⟨[], .fin⟩ ={∅,⊤}=∗ Qfail))) }}
    (App (App (App (Val (@! net.DialTimeout)) (Val #nw)) (Val #a)) (Val #dur))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn, isConn c cn false a ∗ Qok cn) ∨
      (Qfail ∗ ∃ x e, netAddr x ∗ opErr go!"dial" interface.nil x e err ∗
        (sysErr (fun _ => True) e ∨ ⌜e = et ∨ e = ed⌝)) }}

end spec

end net
end Perennial
