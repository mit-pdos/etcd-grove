/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedIndexInformer__OnAdd.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__OnAdd
public import Spec.k8s_io.client_go.tools.cache.sharedProcessor__distribute

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem sharedIndexInformer.OnAdd.wp_proof
    (wp_dist : sharedProcessor.distribute.spec (GF := GF) (hG := hG)) :
    sharedIndexInformer.OnAdd.spec (GF := GF) (hG := hG) := by
  intro s p γp γe evs o b Hbound
  wp_start as ⟨#Hs, HH⟩
  iunfold isSII at Hs
  icases Hs with ⟨#Hp, ⟨%d, #Hd, #Hmd⟩, #Hproc⟩
  iunfold mdOk at Hmd
  icases Hmd with ⟨%di, %Hdi, #Hadd⟩
  subst Hdi
  iunfold infH at HH
  icases HH with ⟨Hsend, Hrd, Hauth⟩
  wp_auto
  ihave #H1 := Hadd $$ %o
  wp_bind (App (Val #(methods di.ty go!"AddObject" di.v)) (Val #o))
  iapply H1
  · itrivial
  inext
  iintro -
  wp_auto
  -- the event recorded in the history: every listener's contract for its next notification
  imod (monoListAuthOwn_update_app (l := evs.map notifOf) [notifOf (Ev.add o b)]) $$ Hauth
    with ⟨Hauth, #Hlb⟩
  ihave #HQ : notifQ γe evs.length (Ev.add o b) $$ []
  · iunfold notifQ
    iapply (monoListIdxOwn_get (l := evs.map notifOf ++ [notifOf (Ev.add o b)]) evs.length
      (notifOf (Ev.add o b)) (by simp)) $$ Hlb
  rw [show interface.mkOk addNotification.ty #(addNotification.mk o b) = notifOf (Ev.add o b)
    from rfl]
  wp_apply (wp_dist p γp (notifQ γe) evs (Ev.add o b) false Hbound)
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
