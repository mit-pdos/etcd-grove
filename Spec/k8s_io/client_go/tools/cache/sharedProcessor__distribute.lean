/-
`(*sharedProcessor).distribute(obj, sync)` (`shared_informer.go:1260`): under the listeners' read
lock, once the listeners are started (or there are none), the notification added to every
(syncing) listener. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the processor and
listeners).
-/
module

public import Proof.k8s_io.client_go.tools.cache.ProcDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`p.distribute(notifOf e, sync)`**, by the sender (`procSend`, having sent the events `E`),
with a reader slot of the listeners' lock and the event's persistent contract `QP E.length e`:
every listener has the event's notification sent (`addCh` is unbuffered: each `add` returns once
the listener's `pop` received it). In an execution of fewer than `2^63` Go steps (`add`'s). -/
abbrev sharedProcessor.distribute.spec : Prop :=
  ∀ (p : Loc) (γp : ProcNames) (QP : Nat → Ev → IProp GF) (E : List Ev) (e : Ev) (sync : Bool),
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isProc p ∗
      procReader p γp ∗ procSend γp QP E ∗ □ QP E.length e }}
    (App (App (Val (p @!! go.GoType.PointerType sharedProcessor.ty @!! go!"distribute"))
      (Val #(notifOf e))) (Val #sync))
  {{ RET #(); procReader p γp ∗ procSend γp QP (E ++ [e]) }}

end spec

end cache
end EtcdGrove
end Perennial
