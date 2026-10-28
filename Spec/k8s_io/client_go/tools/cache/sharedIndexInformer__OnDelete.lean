/-
`(*sharedIndexInformer).OnDelete(old)` (`shared_informer.go:1137`): the delete distributed to the listeners. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the processor and listeners).
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

/-- **`s.OnDelete(o)`** with the informer's view `infH` of the events `evs` it handled: the delete
is the `evs.length`-th event, sent to every listener. In an execution of fewer than `2^63` Go
steps. -/
abbrev sharedIndexInformer.OnDelete.spec : Prop :=
  ∀ (s p : Loc) (γp : ProcNames) (γe : GName) (evs : List Ev) (o : GoInterface),
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isSII s p ∗
      infH p γp γe evs }}
    (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"OnDelete")) (Val #o))
  {{ RET #(); infH p γp γe (evs ++ [Ev.delete o]) }}

end spec

end cache
end EtcdGrove
end Perennial
