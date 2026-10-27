/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__keyOf.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__keyOf

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

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

theorem RealFIFO.keyOf.wp_proof :
    RealFIFO.keyOf.spec (GF := GF) (hG := hG) := by
  intro f OK kf obj
  wp_start as ⟨#Hkf, #Hkey, #Hany, %harg, HOK⟩
  iunfold keyNoErr at Hkey
  iunfold keyAny at Hany
  rcases harg with ⟨t, v, rfl⟩ | ⟨d, t, w, rfl, hd, ht⟩
  · ihave #HOK' := HOK $$ %(⟨t, v, rfl⟩)
    (try wp_auto)
    wp_apply Hkey $$ [$HOK']
    iintro %k %err %hk
    subst hk
    (try wp_auto)
    iapply HΦ
    ipureintro; intro _; rfl
  · (try wp_auto)
    rw [hd]
    (try wp_auto)
    simp only [ht, ↓reduceIte, decide_false]
    (try wp_auto)
    wp_apply Hany
    iintro %k %err -
    (try wp_auto)
    iapply HΦ
    ipureintro
    rintro ⟨t', v', h⟩
    simp only [interface.mkOk, GoInterface.ok.injEq] at h
    exfalso
    have h1 := congrArg GoInterfaceOk.ty h
    simp only at h1
    unfold Delta.ty at h1
    cases h1

end proof

end cache
end EtcdGrove
end Perennial
