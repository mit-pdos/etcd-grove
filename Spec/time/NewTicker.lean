/-
`time.NewTicker`, of Go's `time` package: the trust boundary (Perennial does not translate tickers
and its runtime's timers are not modelled). Lean-first (no Rocq counterpart), as Perennial's
`time.NewTimer` (`Perennial/Proof/time.lean`).

A `*Ticker` from `NewTicker` is `isTicker t`: its `C` field holds, for good, a channel on which a
receive may yield some time (a bag of times, `isChanBag`, with no logical content). The specs say
nothing about *when* (or whether) a tick arrives, which over-approximates Go's tickers (sound for
safety). Go panics on a non-positive period (`NewTicker`, `Ticker.Reset`): the specs require a
positive one.
-/
module

public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `t` is a `*Ticker` made by `NewTicker` (persistent): not nil, its channel `C` a bag of times. -/
def time.isTicker (t : Loc) : IProp GF :=
  iprop(⌜t ≠ null⌝ ∗ ∃ (ch : Loc) (γ : ChanNames), structFieldRef time.Ticker go!"C" t ↦□ ch ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)))

instance time.isTicker_persistent (t : Loc) : Persistent (time.isTicker (GF := GF) t) := by
  unfold time.isTicker; infer_instance

/-- `time.NewTicker(d)` of a positive period: a `*Ticker` (`isTicker`). -/
abbrev time.NewTicker.spec : Prop :=
  ∀ d : time.Duration,
  {{ (⌜0 < sint.Z d⌝ : IProp GF) }}
    (App (Val (@! time.NewTicker)) (Val #d))
  {{ (t : Loc), RET #t; time.isTicker t }}

end spec

end EtcdGrove
end Perennial
