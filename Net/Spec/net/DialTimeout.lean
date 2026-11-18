/-
`net.DialTimeout("tcp", a, timeout)` for an address `a` of the plan (`netPlan`; `DialTimeout.impl`,
`Net/TrustedCode/net.lean`, D19): as `net.Dial` (`Dial.spec`: the extension's `Dial`, D8, D16),
but a failure's `Err` is an `*os.SyscallError` or a timeout, `net`'s `errTimeout` (`et`) or
`poll.ErrDeadlineExceeded`'s value (`ed`): both occur (`TestDialTimeoutAccepted`). The timeout's
value is not modeled. Proved in `Net/Proof/net/DialTimeout.lean`.
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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev DialTimeout.spec : Prop :=
  ∀ (a h : GoString) (dur : w64) (et ed : GoInterface) (Qfail : IProp GF) (Qok : Nat → IProp GF),
  {{ netPlan (extGlobalGS netExt (G := hG.goose_globalGS)) a h ∗ globalAddr errTimeout ↦□ et ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      (Qfail ∧
        |={⊤,∅}=> ∃ S, netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a S ∗
          ∀ cn, ⌜cn ∉ S⌝ -∗ netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a (S ∪ {[cn]}) -∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
            netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn true -∗
            ((netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ={∅,⊤}=∗ Qok cn) ∧
             (netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false { NetEnd.fresh with closed := true } -∗
              netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ⟨[], .fin⟩ ={∅,⊤}=∗ Qfail))) }}
    (App (App (App (Val (@! net.DialTimeout)) (Val #(go!"tcp"))) (Val #a)) (Val #dur))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn, isConn c cn false a ∗ Qok cn) ∨
      (Qfail ∗ ∃ x e, netAddr x ∗ opErr go!"dial" interface.nil x e err ∗
        (sysErr (fun _ => True) e ∨ ⌜e = et ∨ e = ed⌝)) }}

end spec

end net
end Perennial
