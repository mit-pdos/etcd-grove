/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/time.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
Cross-package specs of `pkg/time`: the `Time` interface holding a `*Real` (`isTime`), its `Now`
(any value: time is not modeled), and the `*Timer` (`isTimer tm st`, exclusive, `st` its stored
state): `NewTimer`, `Reset`, `Done` (any bool), `SetState`, `State`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.time.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The `Time` interface value `t` holds a `*Real`. -/
def time.isTime [GooseExts] [GoGlobalContext] (t : GoInterface) : Prop :=
  ∃ r : Loc, t = interface.mkOk (go.GoType.PointerType time.Real.ty) #r

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- The `*Timer` `tm` (over a `*Real` time) stores the state `st` (exclusive). -/
def time.isTimer (tm : Loc) (st : GoInterface) : IProp GF :=
  iprop(∃ (start ticks : w64) (t : time.Time) (act : GoFunc),
    tm ↦ time.Timer.mk start ticks t st act ∗ ⌜time.isTime t⌝)

instance time.isTimer_timeless (tm : Loc) (st : GoInterface) :
    Timeless (time.isTimer (GF := GF) (hG := hG) tm st) := by
  unfold time.isTimer; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : time.Assumptions]

set_option goose.wp.extras true

/-- `NewReal()`: a `*Real`, which as a `Time` is `isTime`. -/
abbrev time.NewReal.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time }}
    (App (Val (@! time.NewReal)) (Val #()))
  {{ (r : Loc), RET #r; ⌜time.isTime (interface.mkOk (go.GoType.PointerType time.Real.ty) #r)⌝ }}

/-- `t.Now()` through the `Time` interface: some time. -/
abbrev time.Time.Now.spec : Prop :=
  ∀ (t : GoInterface), time.isTime t →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time }}
    (App (App (Val (GoInstruction (MethodResolve time.Time.ty go!"Now"))) (Val #t)) (Val #()))
  {{ (n : w64), RET #n; True }}

/-- `NewTimer(t, ticks)`: a timer with no state. -/
abbrev time.NewTimer.spec : Prop :=
  ∀ (t : GoInterface) (ticks : w64), time.isTime t →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time }}
    (App (App (Val (@! time.NewTimer)) (Val #t)) (Val #ticks))
  {{ (tm : Loc), RET #tm; time.isTimer tm interface.nil }}

/-- `tm.Reset()`. -/
abbrev time.Timer.Reset.spec : Prop :=
  ∀ (tm : Loc) (st : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time ∗
      time.isTimer tm st }}
    (App (Val (tm @!! go.GoType.PointerType time.Timer.ty @!! go!"Reset")) (Val #()))
  {{ RET #(); time.isTimer tm st }}

/-- `tm.Done()`: some bool. -/
abbrev time.Timer.Done.spec : Prop :=
  ∀ (tm : Loc) (st : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time ∗
      time.isTimer tm st }}
    (App (Val (tm @!! go.GoType.PointerType time.Timer.ty @!! go!"Done")) (Val #()))
  {{ (b : Bool), RET #b; time.isTimer tm st }}

/-- `tm.SetState(st')`. -/
abbrev time.Timer.SetState.spec : Prop :=
  ∀ (tm : Loc) (st st' : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time ∗
      time.isTimer tm st }}
    (App (Val (tm @!! go.GoType.PointerType time.Timer.ty @!! go!"SetState")) (Val #st'))
  {{ RET #(); time.isTimer tm st' }}

/-- `tm.State()`: the stored state, and whether it is not `nil`. -/
abbrev time.Timer.State.spec : Prop :=
  ∀ (tm : Loc) (st : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time ∗
      time.isTimer tm st }}
    (App (Val (tm @!! go.GoType.PointerType time.Timer.ty @!! go!"State")) (Val #()))
  {{ RET (PairV #st #(decide (st ≠ interface.nil))); time.isTimer tm st }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
