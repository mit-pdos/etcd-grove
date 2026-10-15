/-
`time.Since`, of Go's `time` package, as `syncWatchersLoop` needs it: **an assumption about the
clock**, not Go's guarantee. Perennial's `time.wp_Since` returns any duration; Go's, of a time with
a monotonic reading (`time.Now()`'s), is the monotonic clock's advance, at least `0`. The watchable
store's `syncWatchersLoop` resets its ticker to the duration of its `syncWatchers` call
(`delayTicker.Reset(syncDuration)`), which panics if it is `0`: this spec assumes the clock
advances over such a call (a positive duration). See notes: a coarse monotonic clock (or one that
does not advance) makes `syncWatchersLoop` panic when it shortens its period.
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

/-- `time.Since(t)`: a positive duration (the assumption above). -/
abbrev time.Since.spec : Prop :=
  ∀ t : time.Time,
  {{ (True : IProp GF) }}
    (App (Val (@! time.Since)) (Val #t))
  {{ (d : w64), RET #d; ⌜0 < sint.Z d⌝ }}

end spec

end EtcdGrove
end Perennial
