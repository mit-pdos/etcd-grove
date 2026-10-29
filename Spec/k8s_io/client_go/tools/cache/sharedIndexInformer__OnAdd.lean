/-
`(*sharedIndexInformer).OnAdd(obj, isInInitialList)` (`shared_informer.go:1107`): the object handed to the mutation detector, the add distributed to the listeners. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the processor and listeners).
-/
module

public import Proof.k8s_io.client_go.tools.cache.SIIDefs

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

/-- **`s.OnAdd(o, b)`** with the informer's view `infH` of the events `evs` it handled: the add
is the `evs.length`-th event, sent to every listener. In an execution of fewer than `2^63` Go
steps (`distribute`'s). -/
abbrev sharedIndexInformer.OnAdd.spec : Prop :=
  ∀ (s p : Loc) (γp : ProcNames) (γe : GName) (evs : List Ev) (o : GoInterface) (b : Bool),
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isSII s p ∗
      infH p γp γe evs }}
    (App (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"OnAdd")) (Val #o))
      (Val #b))
  {{ RET #(); infH p γp γe (evs ++ [Ev.add o b]) }}

end spec

end cache
end EtcdGrove
end Perennial
