/-
**`Tracer.Start` from a `txnCtx`** (k8s 7f-4, T-f): the triple as it was before the premise admitted a
stream handler's weak context (`srvCtxWeak`), derived from the current one. What the request path's
callers use. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- **`Tracer.Start` on a `txnCtx`**: the context returned is one, and an `isContext` if `ctx` is
(the triple of `traceutil.Tracer.Start.spec` with the premise's left disjunct, and its span fact
`trace.spanValOk` from the library values `context.libCtxOk` the request path carries). -/
theorem traceutil.Tracer.Start.spec_txn (hTS : traceutil.Tracer.Start.spec (GF := GF) (hG := hG)) :
  ∀ (tr ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (name : GoString)
    (opts : GoSlice),
  {{ globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr ∗
      mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx }}
    (App (App (App (Val #(methods tr.ty go!"Start" tr.v)) (Val #(GoInterface.ok ctx))) (Val #name))
      (Val #opts))
  {{ (ctx' : GoInterfaceOk) (sp : GoInterface), RET (PairV #(GoInterface.ok ctx') #sp);
      (∃ vs : GMap GoInterface GoInterface, mvcc.txnCtx ctx' { cd with Values := vs } ∗
        (context.isContext ctx cd -∗ context.isContext ctx' { cd with Values := vs })) ∗
      □ (∀ o : Option Loc, traceutil.ctxTraceIs ctx o -∗ traceutil.ctxTraceIs ctx' o) ∗
      ⌜metadata.incomingOf (GoInterface.ok ctx') = metadata.incomingOf (GoInterface.ok ctx)⌝ ∗
      trace.isSpan sp ∗ □ (trace.spanCtxOk ctx -∗ trace.spanCtxOk ctx') ∗
      □ (context.startTimeOk ctx -∗ context.startTimeOk ctx') ∗
      □ (context.libCtxOk ctx -∗ context.libCtxOk ctx') }} := by
  intro tr ctx cd name opts
  iintro %Φ ⟨#Htr, #Htxn, #Hlib⟩ HΦ
  ihave #Hlib' := Hlib
  iunfold context.libCtxOk at Hlib'
  icases Hlib' with ⟨-, -, -, #Hsp⟩
  iapply (hTS tr ctx cd name opts) $$ []
  · iframe #
  iintro !> %ctx' %sp ⟨⟨%vs, #Ht, Hw⟩, -, #Hrest⟩
  iapply HΦ
  isplitl [Hw]
  · iexists vs
    iframe Hw
    iapply Ht $$ Htxn
  iexact Hrest

end lemmas

end EtcdGrove
end Perennial
