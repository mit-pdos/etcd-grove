/-
**The shared informer meets the handler contract** `handlerOk` (`InformerDefs.lean`) that
`processDeltas`/`handleDeltas` take as a premise, with its view `infH` of the events it handled
(`SIIDefs.lean`): from its `OnAdd`/`OnUpdate`/`OnDelete` (`sharedIndexInformer__On*.lean`), each
of which distributes the event to every listener. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the processor and listeners).
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__OnAdd
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__OnUpdate
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__OnDelete

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The informer is a handler** (`handlerOk`) for the objects `OK` (with `meta.Accessor`
returning on them, `accRet`) and the events' facts `EF`, its delivered events `infH p γp γe EF`:
each event it is handed is distributed to every listener, in order, with its facts. In an
execution of fewer than `2^63` Go steps. -/
theorem sharedIndexInformer_handlerOk
    (wp_OnAdd : sharedIndexInformer.OnAdd.spec (GF := GF) (hG := hG))
    (wp_OnUpdate : sharedIndexInformer.OnUpdate.spec (GF := GF) (hG := hG))
    (wp_OnDelete : sharedIndexInformer.OnDelete.spec (GF := GF) (hG := hG))
    (Hbound : receiptBound GF ≤ 2 ^ 63)
    (s p : Loc) (γp : ProcNames) (γe : GName) (OK : GoInterface → IProp GF)
    (EF : Ev → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isSII s p ∗ accRet OK ⊢
      handlerOk OK EF (interface.mkOk (go.GoType.PointerType sharedIndexInformer.ty) #s)
        (infH p γp γe EF) := by
  haveI : ReceiptBoundLe GF (2 ^ 63) := ⟨Hbound⟩
  iintro ⟨#Hpkg, #Hs, #Hacc⟩
  unfold handlerOk
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    iintro %evs %o %b %Φ
    imodintro
    iintro ⟨HH, -, #HE⟩ HΦ
    iapply (wp_OnAdd s p γp γe EF evs o b) $$ [$Hpkg $Hs $HH $HE] HΦ
  isplitr
  · imodintro
    iintro %evs %old %new %Φ
    imodintro
    iintro ⟨HH, #Hold, #Hnew, #HE⟩ HΦ
    iapply (wp_OnUpdate s p γp γe EF evs OK old new) $$ [$Hpkg $Hs $Hacc $Hold HH $HE] HΦ
    iframe
    iunfold okNil; iright; iexact Hnew
  · imodintro
    iintro %evs %o %Φ
    imodintro
    iintro ⟨HH, -, #HE⟩ HΦ
    iapply (wp_OnDelete s p γp γe EF evs o) $$ [$Hpkg $Hs $HH $HE] HΦ

end proof

end cache
end EtcdGrove
end Perennial
