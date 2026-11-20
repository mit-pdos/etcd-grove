/- Lean-first (no Rocq counterpart).

`realRequest.wp_proof` (k8s 7g step 5): a case on the input's kind; each request's fields from its callees'
posts, the create's `*Obj` made read-only.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.listOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.splitKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.preconditions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.validateFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.tryUpdateFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cachedObj

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem realRequest.wp_proof
    (wp_listOptions : listOptions.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_splitKey : splitKey.spec (GF := GF) (hG := hG))
    (wp_preconditions : preconditions.spec (GF := GF) (hG := hG))
    (wp_validateFor : validateFor.spec (GF := GF) (hG := hG))
    (wp_tryUpdateFor : tryUpdateFor.spec (GF := GF) (hG := hG))
    (wp_cachedObj : cachedObj.spec (GF := GF) (hG := hG)) :
    realRequest.spec (GF := GF) (hG := hG) := by
  intro x hx
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_listOptions
    (try wp_auto)
    iapply HΦ
    unfold reqRep reqPin
    rw [if_pos Hif, if_neg (by rw [Hif]; decide), if_neg (by rw [Hif]; decide)]
    isplit <;> ipureintro
    · exact ⟨rfl, rfl, rfl⟩
    · trivial
  wp_apply wp_storeKey
  (try wp_auto)
  wp_if_destruct
  · iapply wp_fupd
    wp_apply wp_splitKey
    (try wp_auto)
    irename «$v0» => Ho
    ipersist Ho
    imodintro
    iapply HΦ
    unfold reqRep reqPin
    rw [if_neg (by rw [Hif]; decide), if_pos Hif, if_neg (by rw [Hif]; decide),
      if_neg (by rw [Hif]; decide)]
    isplitl
    · isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexists «$v0_ptr»
      isplitr
      · ipureintro; rfl
      iExactEq Ho; rfl
    · ipureintro; trivial
  rename_i h4
  wp_if_destruct
  · wp_apply wp_preconditions as %pp Hpp
    wp_apply wp_validateFor as %vf ⟨%hvf, #Hvd, #Hvp⟩
    wp_apply wp_cachedObj as %cx -
    (try wp_auto)
    iapply HΦ
    unfold reqRep reqPin
    rw [if_neg h4, if_neg (by rw [Hif]; decide), if_pos Hif, if_pos Hif]
    dsimp only
    iframe Hpp Hvd Hvp
    ipureintro; exact ⟨rfl, rfl, hvf⟩
  rename_i h1
  wp_if_destruct
  · wp_apply wp_tryUpdateFor _ hx as %uf ⟨%huf, #Hud, #Hup⟩
    wp_apply wp_preconditions as %pp Hpp
    wp_apply wp_cachedObj as %cx -
    (try wp_auto)
    iapply HΦ
    unfold reqRep reqPin
    rw [if_neg h4, if_neg (by rw [Hif]; decide), if_neg (by rw [Hif]; decide), if_pos Hif,
      if_neg (by rw [Hif]; decide), if_pos Hif]
    dsimp only
    iframe Hpp Hud Hup
    ipureintro; exact ⟨rfl, rfl, rfl, huf⟩
  rename_i h2
  iapply HΦ
  unfold reqRep reqPin
  rw [if_neg h4, if_neg h1, if_neg h2, if_neg Hif, if_neg h2, if_neg Hif]
  isplit <;> ipureintro
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · trivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
