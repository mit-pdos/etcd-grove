/-
`handleWatch(ctx, start, w, store, expectedType, expectedGVK, name, expectedTypeName,
setLastSyncResourceVersion, clock, errCh)` (`reflector.go:944`): `handleAnyWatch` with
`exitOnWatchListBookmarkReceived` false, its error returned. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md`, fifth round.
-/
module

public import Spec.k8s_io.client_go.tools.cache.handleAnyWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache apimodel

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`handleWatch(...)`**: as `handleAnyWatch`, its error returned. -/
abbrev handleWatch.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (dch : GoChan) (γd : ChanNames) (start : time.Time) (w : GoInterface)
    (γa : ApiNames) (γw : WatchNames) (r : Res) (bm : Bool) (inits : List Obj)
    (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (et : reflect.Type')
    (name tname : GoString) (cb : GoFunc) (clk : k8s_io.utils.clock.RealClock) (errCh : GoChan)
    (n : Nat) (p : Pos') (L : Nat → Pos' → IProp GF) (C : Nat → Pos' → GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ stableCtx ctx dch γd ∗
      watchAt w γa γw r go!"" bm inits ∗ watchCons γw n p ∗ L n p ∗ isFIFO f γ OK ∗
      typeOfOk et r ∗ errChOk errCh ∗ evStepOk γa γw r bm inits γ OK L C ∗ cbOk cb C L }}
    (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! k8s_io.client_go.tools.cache.handleWatch))
      (Val #(GoInterface.ok ctx))) (Val #start)) (Val #w))
      (Val #(interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f : ReflectorStore)))
      (Val #et)) (Val #(null : Loc))) (Val #name)) (Val #tname)) (Val #cb))
      (Val #(interface.mkOk k8s_io.utils.clock.RealClock.ty #clk : k8s_io.utils.clock.Clock)))
      (Val #errCh))
  {{ (err : GoInterface), RET #err; ∃ (n' : Nat) (p' : Pos'), watchCons γw n' p' ∗ L n' p' }}

end spec

end cache
end EtcdGrove
end Perennial
