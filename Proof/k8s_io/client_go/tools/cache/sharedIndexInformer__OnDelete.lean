/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedIndexInformer__OnDelete.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__OnDelete
public import Spec.k8s_io.client_go.tools.cache.sharedProcessor__distribute

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

theorem sharedIndexInformer.OnDelete.wp_proof
    (wp_dist : sharedProcessor.distribute.spec (GF := GF) (hG := hG)) :
    sharedIndexInformer.OnDelete.spec (GF := GF) (hG := hG) := by
  intro s p γp γe evs o Hbound
  wp_start as ⟨#Hs, HH⟩
  iunfold isSII at Hs
  icases Hs with ⟨#Hp, -, #Hproc⟩
  iunfold infH at HH
  icases HH with ⟨Hsend, Hrd, Hauth⟩
  wp_auto
  imod (monoListAuthOwn_update_app (l := evs.map notifOf) [notifOf (Ev.delete o)]) $$ Hauth
    with ⟨Hauth, #Hlb⟩
  ihave #HQ : notifQ γe evs.length (Ev.delete o) $$ []
  · iunfold notifQ
    iapply (monoListIdxOwn_get (l := evs.map notifOf ++ [notifOf (Ev.delete o)]) evs.length
      (notifOf (Ev.delete o)) (by simp)) $$ Hlb
  rw [show interface.mkOk deleteNotification.ty #(deleteNotification.mk o) = notifOf (Ev.delete o)
    from rfl]
  wp_apply (wp_dist p γp (notifQ γe) evs (Ev.delete o) false Hbound)
    $$ [$Hpkg $Hproc $Hrd $Hsend $HQ] as ⟨Hrd, Hsend⟩
  iapply HΦ
  iunfold infH
  iframe
  simp only [List.map_append, List.map_cons, List.map_nil]
  iexact Hauth

end proof

end cache
end EtcdGrove
end Perennial
