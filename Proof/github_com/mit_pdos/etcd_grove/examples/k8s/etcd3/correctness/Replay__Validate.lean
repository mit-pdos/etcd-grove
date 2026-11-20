/-
Lean-first (no Rocq counterpart).

The proof of `(*Replay).Validate`, on the accepting run: the switch on the request's operation, a get
to `validateGet`, a list to `validateList`, a write passes.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__Validate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__validateGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__validateList

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Replay.Validate.wp_proof
    (wp_vGet : Replay.validateGet.spec (GF := GF) (hG := hG))
    (wp_vList : Replay.validateList.spec (GF := GF) (hG := hG)) :
    Replay.Validate.spec (GF := GF) (hG := hG) := by
  intro rp R r ro x out hpre hlx hkey hok
  wp_start as ⟨#HR, #Hreq, #Hresp⟩
  ihave #Hreq0 := Hreq
  unfold rvalidateL at hok
  iunfold reqRep at Hreq
  by_cases h4 : x.Kind' = W64 4
  · isimp only [h4, ↓reduceIte] at Hreq
    simp only [h4, ↓reduceIte] at hok
    icases Hreq with %Hr
    wp_auto
    rw [Hr.1]
    wp_auto
    wp_apply (wp_vList rp R r ro x out h4 hpre (hlx h4) hok) $$ [] as %err %herr
    · iframe #
    iapply HΦ; ipureintro; exact herr
  simp only [h4, ↓reduceIte] at hok
  by_cases h0 : x.Kind' = W64 0
  · isimp only [h4, ↓reduceIte] at Hreq
    isimp only [h0, ↓reduceIte] at Hreq
    icases Hreq with ⟨%Hr, -⟩
    wp_auto
    rw [Hr.1]
    wp_auto
    iapply HΦ; ipureintro; rfl
  by_cases h1 : x.Kind' = W64 1
  · isimp only [h4, h0, ↓reduceIte] at Hreq
    isimp only [h1, ↓reduceIte] at Hreq
    icases Hreq with ⟨%Hr, -⟩
    wp_auto
    rw [Hr.1]
    wp_auto
    iapply HΦ; ipureintro; rfl
  by_cases h2 : x.Kind' = W64 2
  · isimp only [h4, h0, h1, ↓reduceIte] at Hreq
    isimp only [h2, ↓reduceIte] at Hreq
    icases Hreq with ⟨%Hr, -⟩
    wp_auto
    rw [Hr.1]
    wp_auto
    iapply HΦ; ipureintro; rfl
  simp only [h0, h1, h2, _root_.or_self] at hok
  isimp only [h4, h0, h1, h2, ↓reduceIte] at Hreq
  icases Hreq with %Hr
  wp_auto
  rw [Hr.1]
  wp_auto
  wp_apply (wp_vGet rp R r ro x out h4 h0 h1 h2 hpre (hkey h4) hok) $$ [] as %err %herr
  · iframe #
  iapply HΦ; ipureintro; exact herr

end proof

end k8s_correctness
end EtcdGrove
end Perennial
