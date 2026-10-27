/-
`(*sharedIndexInformer).OnUpdate(old, new)` (`shared_informer.go:1115`): a sync if the resource versions agree; the new object handed to the mutation detector, the update distributed to the (syncing) listeners. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the processor and listeners).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`s.OnUpdate(old, new)`** with the informer's view `infH` of the events `evs` it handled, the
objects `nil` or meeting `OK` (`meta.Accessor` returning on them, `accRet`): the update is the
`evs.length`-th event, sent to every listener (all are syncing, `ProcDefs.lean`). In an execution
of fewer than `2^63` Go steps. -/
abbrev sharedIndexInformer.OnUpdate.spec : Prop :=
  ∀ (s p : Loc) (γp : ProcNames) (γe : GName) (evs : List Ev) (OK : GoInterface → IProp GF)
    (old new : GoInterface),
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isSII s p ∗
      accRet OK ∗ okNil OK old ∗ okNil OK new ∗ infH p γp γe evs }}
    (App (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"OnUpdate"))
      (Val #old)) (Val #new))
  {{ RET #(); infH p γp γe (evs ++ [Ev.update old new]) }}

end spec

end cache
end EtcdGrove
end Perennial
