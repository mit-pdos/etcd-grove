/-
## `(*timeList).Trigger(deadline)`

**Users.** The apply thread (`server.go:985`: `s.applyWait.Trigger(ep.appliedi)` after each applied
batch, with the applied index's fact). One caller at a time in etcd (the apply thread), but the
spec needs no exclusivity. Snippet: `examples/specreq/wait/wait.go` (`ReqWaitTime`).

**Proof sketch.** `Lock`; `last := d` (the invariant's `□ P last` from the caller's `□ P d`: also
when `d` is below the old `last`); for each map entry `t ≤ d`, delete and close its channel with
`□ P t` (downward closure from `□ P d`); `Unlock`.

**Changes.** Unchanged in substance.

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

/-- **Triggers every deadline at most `d`**, with `□ P d`. -/
def timeList.Trigger.spec : Prop :=
  ∀ (tl : Loc) (P : w64 → IProp GF) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ timeListAt tl P ∗ □ P d }}
    (App (Val (tl @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.timeList.ty @!! go!"Trigger"))
      (Val #d))
  {{ RET #(); True }}

end spec
end Wait
end EtcdGrove
end Perennial
