/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/getAttrs.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.objLabels

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem getAttrs.wp_proof
    (wp_objLabels : objLabels.spec (GF := GF) (hG := hG))
    : getAttrs.spec (GF := GF) (hG := hG) := by
  intro p dq o
  wp_start as Hp
  iapply wp_fupd
  wp_auto
  wp_apply (wp_objLabels o) as %lm Hlm
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %fm Hfm
  (try wp_auto)
  wp_apply (wp_mapInsert go.string fm ∅ go!"metadata.name" o.Name') $$ [$Hfm] as Hfm
  (try wp_auto)
  wp_apply (wp_mapInsert go.string fm _ go!"metadata.namespace" o.Namespace') $$ [$Hfm] as Hfm
  (try wp_auto)
  wp_apply (wp_mapInsert go.string fm _ go!"spec.nodeName" o.Node') $$ [$Hfm] as Hfm
  (try wp_auto)
  ipersist Hfm
  ihave Hp : p ↦{dq} o $$ [Namespace Name UID Value Node App ResourceVersion Annotated]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  by_cases ha : o.App' = []
  · rw [if_pos ha]
    icases Hlm with %hlm
    imodintro
    iapply HΦ
    iframe Hp
    unfold mapRO
    isplitl
    · ileft; ipureintro; exact ⟨hlm, by simp [labMapL, ha]⟩
    · iright; unfold fldMapL; iexact Hfm
  · rw [if_neg ha]
    ipersist Hlm
    imodintro
    iapply HΦ
    iframe Hp
    unfold mapRO
    isplitl
    · iright; iexact Hlm
    · iright; unfold fldMapL; iexact Hfm

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
