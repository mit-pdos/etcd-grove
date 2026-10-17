/-
`github.com/jonboulle/clockwork` (names only): what its `Clock` interface's methods do, as the
etcd code here uses them (v3compactor's compactors: etcd#22095, etcd#18472). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `clk` is a `clockwork.Clock` (persistent): `Now()` returns some time; `After(d)` returns a
channel from which a receive yields some time (a bag of times, `isChanBag`, as the cache's
timers). What clockwork's real clock does (`time.Now`, `time.After`); a fake clock's `After`
too (its channel gets a time when the fake time is advanced). -/
def clockwork.isClock (clk : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜clk = GoInterface.ok ci⌝ ∗
    {{ True }} (App (Val #(methods ci.ty go!"Now" ci.v)) (Val #()))
      {{ (t : time.Time), RET #t; True }} ∗
    (∀ d : time.Duration, {{ True }} (App (Val #(methods ci.ty go!"After" ci.v)) (Val #d))
      {{ (ch : Loc) (γ : ChanNames), RET #ch;
          isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }}))

instance clockwork.isClock_persistent (clk : GoInterface) :
    Persistent (clockwork.isClock (GF := GF) clk) := by
  unfold clockwork.isClock; infer_instance

/-- `clk` is a clock whose `After(d)` is called only at durations `d` with `D d` (persistent):
`Now()` returns some time; `After(d)`, for `D d`, a channel of times. The premise of a caller's
spec that says which waits it does (`Revision.Run`: `D := (· = interval)`); a real clock
(`isClock`) is one for every `D` (`isClock_isClockFor`). -/
def clockwork.isClockFor (clk : GoInterface) (D : time.Duration → Prop) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜clk = GoInterface.ok ci⌝ ∗
    {{ True }} (App (Val #(methods ci.ty go!"Now" ci.v)) (Val #()))
      {{ (t : time.Time), RET #t; True }} ∗
    (∀ d : time.Duration, ⌜D d⌝ → {{ True }} (App (Val #(methods ci.ty go!"After" ci.v)) (Val #d))
      {{ (ch : Loc) (γ : ChanNames), RET #ch;
          isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }}))

instance clockwork.isClockFor_persistent (clk : GoInterface) (D : time.Duration → Prop) :
    Persistent (clockwork.isClockFor (GF := GF) clk D) := by
  unfold clockwork.isClockFor; infer_instance

theorem clockwork.isClock_isClockFor (clk : GoInterface) (D : time.Duration → Prop) :
    clockwork.isClock (GF := GF) clk ⊢ clockwork.isClockFor clk D := by
  unfold clockwork.isClock clockwork.isClockFor
  iintro ⟨%ci, %Hci, #HNow, #HAfter⟩
  iexists ci
  isplitr
  · ipureintro; exact Hci
  isplitr
  · iexact HNow
  iintro %d -
  iapply HAfter

end defs

end EtcdGrove
end Perennial
