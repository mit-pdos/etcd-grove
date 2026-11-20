module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.predicate
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem toEvent.wp_proof
    (wp_predicate : predicate.spec (GF := GF) (hG := hG))
    (wp_SM : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    toEvent.spec (GF := GF) (hG := hG) := by
  have wp_Matches := mlistMatches.wp_ok wp_SM wp_LM wp_LE wp_FM wp_FE wp_GA
  intro x ch
  wp_start as -
  wp_auto
  wp_apply wp_predicate
  cases hC : ch.hasCur' <;> cases hP : ch.hasPrev' <;>
    cases hs1 : selOkL x ch.cur' <;> cases hs2 : selOkL x ch.prev'
  all_goals
    iterate 8
      try simp only [hC, hP, hs1, hs2]
      try wp_auto
      try wp_apply wp_Matches $$ [$pred $o] as ⟨pred, o⟩
  all_goals
    iapply HΦ
    ipureintro
    simp [toEventL, chgOf, hC, hP, hs1, hs2, wevOf]

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
