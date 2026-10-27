/-
`clock.RealClock.NewTimer(d)` (`k8s.io/utils/clock`, names-only here: the trust boundary; it is
`&realTimer{timer: time.NewTimer(d)}`). Lean-first; for client-go's delaying queue.
-/
module

public import Proof.k8s_io.utils.clock.Init
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A `*realTimer` (persistent): its `timer` field holds, for good, a `*time.Timer` made by
`time.NewTimer` (Perennial's `time.isTimer`). -/
def clock.realTimerOk (p : Loc) : IProp GF :=
  iprop(∃ (t ch : Loc) (γ : ChanNames),
    structFieldRef k8s_io.utils.clock.realTimer go!"timer" p ↦□ t ∗ time.isTimer t ch γ)

instance clock.realTimerOk_persistent (p : Loc) : Persistent (clock.realTimerOk (GF := GF) p) := by
  unfold clock.realTimerOk; infer_instance

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `RealClock{}.NewTimer(d)`: a `*realTimer` as a `clock.Timer`. -/
abbrev clock.RealClock.NewTimer.spec : Prop :=
  ∀ (c : k8s_io.utils.clock.RealClock) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock }}
    (App (Val (c @!! k8s_io.utils.clock.RealClock.ty @!! go!"NewTimer")) (Val #d))
  {{ (p : Loc), RET #(interface.mkOk (go.GoType.PointerType k8s_io.utils.clock.realTimer.ty) #p :
      k8s_io.utils.clock.Timer); clock.realTimerOk p }}

end spec

end EtcdGrove
end Perennial
