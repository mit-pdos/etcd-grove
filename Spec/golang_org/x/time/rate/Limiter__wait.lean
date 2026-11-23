/-
`(*rate.Limiter).wait(ctx, n, t, newTimer)` (x/time/rate v0.16.0, `rate.go:251-316`: `WaitN`'s body,
over a timer generator, which the tests replace by a fake; rate-wait, 2026-11-23). Lean-first.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Wait
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- **`nt` is a timer generator** (persistent), as `WaitN`'s closure over `time.NewTimer`: `nt(d)`
returns a channel of times whose receive returns (a timer's channel, `isChanBag`: whatever is in it
is a time), a `stop` function returning some `bool`, and an `advance` function (a no-op in
`WaitN`'s; the tests' fake timer moves its clock). -/
def rate.newTimerOk (nt : GoFunc) : IProp GF :=
  iprop(∀ (d : _root_.Perennial.time.Duration),
    {{ True }} (App (Val #nt) (Val #d))
    {{ (ch : Loc) (stop adv : GoFunc) (γ : ChanNames), RET (PairV (PairV #ch #stop) #adv);
        isChanBag (V := _root_.Perennial.time.Time) γ ch (fun _ => iprop(True)) ∗
        ({{ True }} (App (Val #stop) (Val #())) {{ (b : Bool), RET #b; True }}) ∗
        ({{ True }} (App (Val #adv) (Val #())) {{ RET #(); True }}) }})

instance rate.newTimerOk_persistent (nt : GoFunc) : Persistent (rate.newTimerOk (GF := GF) nt) := by
  unfold rate.newTimerOk; infer_instance

/-- **`rl.wait(ctx, n, t, nt)`** of a rate limiter, a context, any count and time, and a timer
generator: returns some error (`rate.Limiter.Wait.spec`). -/
abbrev rate.Limiter.wait.spec : Prop :=
  ∀ (rl : Loc) (c : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (n : w64)
    (t : _root_.Perennial.time.Time) (nt : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ rate.limiterOk rl ∗
      _root_.Perennial.context.isContext c cd ∗ rate.newTimerOk nt }}
    (App (App (App (App (Val (rl @!! go.GoType.PointerType rate.Limiter.ty @!! go!"wait"))
      (Val #(GoInterface.ok c))) (Val #n)) (Val #t)) (Val #nt))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
