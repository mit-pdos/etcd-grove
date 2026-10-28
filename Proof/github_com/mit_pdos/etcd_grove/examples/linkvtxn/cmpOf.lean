/-
Lean-first (no Rocq counterpart).

The proof of `cmpOf`: one branch per kind, `Compare` of the target's comparison.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.cmpOf
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.Value
public import Spec.go_etcd_io.etcd.client.v3.Version
public import Spec.go_etcd_io.etcd.client.v3.ModRevision

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem cmpOf.wp_proof (hValue : EtcdGrove.Value.spec (GF := GF) (hG := hG))
    (hVersion : EtcdGrove.Version.spec (GF := GF) (hG := hG))
    (hMod : EtcdGrove.ModRevision.spec (GF := GF) (hG := hG))
    (hCompare : EtcdGrove.Compare.spec (GF := GF) (hG := hG)) :
    cmpOf.spec (GF := GF) (hG := hG) := by
  intro c m hm
  wp_start as ⟨#Hpkg, #Pc⟩
  wp_auto
  unfold decCmp at hm
  wp_if_destruct
  · rw [if_pos Hif] at hm
    cases hm
    wp_apply hValue c.Key' as %c0 #Hc0
    wp_apply hCompare c0 _ go!"=" .eq _ (.str c.Val') $$ [] as %c1 #Hc1
    · iframe #
      ipureintro
      exact ⟨rfl, ⟨c.Val', rfl, rfl⟩⟩
    wp_auto
    iapply HΦ
    iExactEq Hc1; rfl
  · rw [if_neg Hif] at hm
    wp_if_destruct
    · rw [if_pos Hif] at hm
      cases hm
      wp_apply hVersion c.Key' as %c0 #Hc0
      wp_apply hCompare c0 _ go!"=" .eq _ (.num c.Num') $$ [] as %c1 #Hc1
      · iframe #
        ipureintro
        exact ⟨rfl, ⟨c.Num', Or.inl rfl, rfl⟩⟩
      wp_auto
      iapply HΦ
      iExactEq Hc1; rfl
    · rw [if_neg Hif] at hm
      have hk : c.Kind' = W64 2 := by
        by_cases h : c.Kind' = W64 2
        · exact h
        · rw [if_neg h] at hm; cases hm
      rw [if_pos hk] at hm
      cases hm
      wp_apply hMod c.Key' as %c0 #Hc0
      wp_apply hCompare c0 _ go!"=" .eq _ (.num c.Num') $$ [] as %c1 #Hc1
      · iframe #
        ipureintro
        exact ⟨rfl, ⟨c.Num', Or.inl rfl, rfl⟩⟩
      iapply HΦ
      iExactEq Hc1; rfl

end proof

end linkvtxn
end EtcdGrove
end Perennial
