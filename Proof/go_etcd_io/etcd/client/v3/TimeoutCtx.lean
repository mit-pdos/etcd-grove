/-
A client call's context with a request timeout (`notes/client-timeouts-plan.md`, T1; 2026-10-23):
what the examples' call sites need of `ctx, cancel := context.WithTimeout(context.Background(), d)`,
the pattern of client/v3's documentation -- the context is one the client's call lemmas take
(`ctxOk`: an `isContext`) whose `Err()` returns client errors (`ctxErrClient`, by
`ctxErrClientAllW_of`'s argument: Go's `context.Canceled` and `DeadlineExceeded` are leaf errors,
no `rpctypes.EtcdError`, without a `GRPCStatus` method -- the premises `ContextReadErrs` and
`ContextErrsClient`), and `cancel` is callable from anywhere. Over the trust-boundary spec
`context.WithTimeoutBackground` (the read loop's: Perennial specifies `WithTimeout` of an
`isContext` parent only, and `Background()` is none; `notes/perennial-changes.md`,
"`WithTimeout`/`WithDeadline` of `Background()`").
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Spec.context.WithTimeoutBackground

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions] [fmt_sem : _root_.Perennial.fmt.Assumptions]
variable [rpctypes_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`context.WithTimeout(context.Background(), d)` for a client call** (see the file header): the
context, `ctxOk` and `ctxErrClient` (and the `isContext` they come from, with no outgoing
metadata), and its `cancel`. -/
theorem wp_WithTimeout_bg (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (d : _root_.Perennial.time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (App (Val (@! _root_.Perennial.context.WithTimeout))
        (Val #(interface.ok _root_.Perennial.context.backgroundCtxVal))) (Val #d))
    {{ (ctx' : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF))
        (cancel : GoFunc), RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        ctxOk ctx' cd ∗ ctxErrClient ctx' cd ∗
        (_root_.Perennial.context.isContext ctx' cd ∗
          ⌜metadata.outgoingOf (GoInterface.ok ctx') = none⌝) }} := by
  iintro %Φ #Hpkg HΦ
  ihave #Hcci : _root_.Perennial.context.isClosedchanInit (GF := GF) $$ []
  · iapply _root_.Perennial.context.isClosedchanInit_of_init
    iexact Hpkg
  ihave #Hall := ctxErrClientAllW_of wp_ErrAny hAs $$ Hpkg
  iunfold ctxErrClientAllW at Hall
  wp_apply hWT d $$ [] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx, %Hv⟩
  · iframe #
  iapply HΦ
  iframe #
  isplitr
  · iapply ctxOk_of_isContext
    iexact Hctx
  isplitl
  · iapply Hall
    iexact Hctx
  ipureintro; exact Hv

end proof

end client
end EtcdGrove
end Perennial
