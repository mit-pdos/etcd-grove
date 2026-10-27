/-
`clock.RealClock.NewTicker(d)` (`k8s.io/utils/clock`, names-only here: the trust boundary; it is
`&realTicker{ticker: time.NewTicker(d)}`, which panics for `d ≤ 0`). Lean-first.
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

/-- A `*realTicker` (persistent): its `ticker` field holds, for good, a `*time.Ticker` made by
`time.NewTicker` (Perennial's `time.isTicker`). -/
def clock.realTickerOk (p : Loc) : IProp GF :=
  iprop(∃ (t ch : Loc) (γ : ChanNames),
    structFieldRef k8s_io.utils.clock.realTicker go!"ticker" p ↦□ t ∗ time.isTicker t ch γ)

instance clock.realTickerOk_persistent (p : Loc) :
    Persistent (clock.realTickerOk (GF := GF) p) := by
  unfold clock.realTickerOk; infer_instance

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `RealClock{}.NewTicker(d)`, `d > 0`: a `*realTicker` as a `clock.Ticker`. -/
abbrev clock.RealClock.NewTicker.spec : Prop :=
  ∀ (c : k8s_io.utils.clock.RealClock) (d : time.Duration),
  0 < sint.Z d →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock }}
    (App (Val (c @!! k8s_io.utils.clock.RealClock.ty @!! go!"NewTicker")) (Val #d))
  {{ (p : Loc), RET #(interface.mkOk (go.GoType.PointerType k8s_io.utils.clock.realTicker.ty) #p :
      k8s_io.utils.clock.Ticker); clock.realTickerOk p }}

end spec

end EtcdGrove
end Perennial
