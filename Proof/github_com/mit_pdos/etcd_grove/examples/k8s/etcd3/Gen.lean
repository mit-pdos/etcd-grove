module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache__get
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genFrom
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Gen.wp_proof (wp_get : cache.get.spec (GF := GF) (hG := hG))
    (wp_genFrom : genFrom.spec (GF := GF) (hG := hG)) :
    Gen.spec (GF := GF) (hG := hG) := by
  intro c tbl id
  wp_start as #Hc
  wp_auto
  wp_apply wp_get c tbl id $$ [Hc] as %o %ok #Ho
  · iframe Hc
  (try wp_auto)
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n _
  (try wp_auto)
  wp_apply wp_genFrom n id o ok as %x %Hx
  (try wp_auto)
  iapply HΦ
  isplitr
  · ipureintro; exact Hx.1
  unfold cachedIn
  by_cases hu : x.UseCached' = true
  · obtain ⟨hok, hc⟩ := Hx.2 hu
    simp only [hu, ↓reduceIte]
    isimp only [hok, ↓reduceIte] at Ho
    rw [hc]; iexact Ho
  · simp only [hu, Bool.false_eq_true, ↓reduceIte]
    itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
