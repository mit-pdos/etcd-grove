/-
## `wait.NewTimeList()`

**Users.** `EtcdServer.start` (`server.go:568`: `s.applyWait`, the applied index's waiters).
Snippet: `examples/specreq/wait/wait.go` (`ReqWaitTime`).

**Proof sketch.** Allocates the struct with an empty map and `lastTriggerDeadline = 0`; the lock
invariant `□ P last ∗ (each map entry's channel open, with its deadline)`, at `last = 0` from the
caller's `□ P 0`.

**Changes.** The old spec (`specs-ref`'s `NewTimeList.lean`) is the same in substance; `P`'s
downward closure is now a premise (`Wait` returns `closec` for any `d ≤ last`, and `Trigger` may
lower `last`: both need it).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.wait.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Wait

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

/-- **A new time list over `P`** (downward closed, holding at `0`). -/
def NewTimeList.spec : Prop :=
  ∀ (P : w64 → IProp GF),
  (∀ a b : w64, uint.nat b ≤ uint.nat a → P a ⊢ P b) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ □ P (W64 0) }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.wait.NewTimeList)) (Val #()))
  {{ (tl : Loc), RET #tl; timeListAt tl P }}

end spec
end Wait
end EtcdGrove
end Perennial
