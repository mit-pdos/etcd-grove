/-
**Lenses into a DaemonSet's deep ownership** for the sync path's glue proofs (fields the
controller reads off the DaemonSet it got from its lister, read-only for good). Lean-first.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [apps_sem : k8s_io.api.apps.v1.Assumptions]

/-- **The DaemonSet's update strategy type** (`ds.Spec.UpdateStrategy.Type`), read-only. -/
theorem dsAt_updType (ds : Loc) (d : kd.apps.DaemonSet) :
    dsAt (GF := GF) ds DFrac.discard d ⊢
      ds.[k8s_io.api.apps.v1.DaemonSet, go!"Spec"].[k8s_io.api.apps.v1.DaemonSetSpec,
        go!"UpdateStrategy"].[k8s_io.api.apps.v1.DaemonSetUpdateStrategy, go!"Type"] ↦□
        d.Spec'.UpdateStrategy'.Type' := by
  unfold dsAt
  iintro ⟨%v, Hl, Hd⟩
  iStructNamed Hl
  iStructNamedPrefix Spec "S"
  iStructNamedPrefix SUpdateStrategy "U"
  iunfold kd.apps.DaemonSet.own at Hd
  icases Hd with ⟨-, -, DSpec, -⟩
  iunfold kd.apps.DaemonSetSpec.own at DSpec
  icases DSpec with ⟨-, -, DU, -, -⟩
  iunfold kd.apps.DaemonSetUpdateStrategy.own at DU
  icases DU with ⟨%hty, -⟩
  rw [← hty]
  iexact UType'

/-- A selector's `MatchLabels` map (`nil` for none: an empty map). -/
theorem ownMapD_lsml (m : GoMap) (o : Option (GMap GoString GoString)) :
    (ownMapD (K := GoString) (V := GoString) m DFrac.discard o : IProp GF) ⊢
      (⌜m = null ∧ GMap.size (o.getD ∅) = 0⌝ ∨ m ↦${DFrac.discard} (o.getD ∅)) := by
  cases o with
  | none =>
    unfold ownMapD
    iintro %h
    ileft
    ipureintro
    exact ⟨h, GMap.map_size_empty⟩
  | some M =>
    simp only [ownMapD, Option.getD_some]
    iintro H
    iright
    iexact H

/-- Basic deep values: the slices' elements are equal. -/
theorem bigSepL2_base_eq (l1 l2 : List GoString) :
    ([∗list] x;e ∈ l1;l2, ownBaseD (GF := GF) x DFrac.discard e) ⊢ ⌜l1 = l2⌝ := by
  induction l1 generalizing l2 with
  | nil =>
    iintro H
    ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H
    ipureintro; exact h.symm
  | cons x xs ih =>
    iintro H
    ihave ⟨%y, %ys, %hl, Hy, Hys⟩ := BigSepL2.bigSepL2_cons_inv_left.1 $$ H
    iunfold ownBaseD at Hy
    icases Hy with %hxy
    ihave %hr := ih ys $$ Hys
    ipureintro
    rw [hl, hxy, hr]

/-- The selector model of a `LabelSelector`'s deep value. -/
def selVOf (s : kd.meta.LabelSelector) : labels.SelV :=
  ⟨s.MatchLabels'.getD ∅, s.MatchExpressions'.map (fun r => ⟨r.Key', r.Operator', r.Values'⟩)⟩

theorem selOf_eq (d : kd.apps.DaemonSet) : selOf d = d.Spec'.Selector'.map selVOf := rfl

/-- A selector's requirements, from their deep ownership (read-only). -/
theorem lsReqs_of (vs : List k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelectorRequirement)
    (ds : List kd.meta.LabelSelectorRequirement) :
    ([∗list] x;e ∈ vs;ds, kd.meta.LabelSelectorRequirement.own (GF := GF) x DFrac.discard e) ⊢
      [∗list] i ↦ r ∈ vs, ∃ (q : labels.Req) (vals : List GoString),
        ⌜(ds.map (fun r => (⟨r.Key', r.Operator', r.Values'⟩ : labels.Req)))[i]? = some q ∧
          r.Key' = q.key ∧ r.Operator' = q.op ∧ q.vals = vals⌝ ∗ r.Values' ↦*{DFrac.discard} vals := by
  induction vs generalizing ds with
  | nil =>
    iintro -
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons v vs ih =>
    iintro H
    ihave ⟨%e, %es, %hl, Hv, Hrest⟩ := BigSepL2.bigSepL2_cons_inv_left.1 $$ H
    subst hl
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hv]
    · iunfold kd.meta.LabelSelectorRequirement.own at Hv
      icases Hv with ⟨%hk, %hop, Hvals⟩
      iunfold ownSliceD at Hvals
      icases Hvals with ⟨%vals, Hsl, Hall⟩
      ihave %hv := bigSepL2_base_eq vals e.Values' $$ Hall
      iexists ⟨e.Key', e.Operator', e.Values'⟩, vals
      iframe
      ipureintro
      exact ⟨rfl, hk, hop, hv.symm⟩
    · simp only [List.map_cons, List.getElem?_cons_succ]
      iapply ih es
      iexact Hrest

/-- **A `*LabelSelector`'s deep ownership** (read-only) holds its selector model. -/
theorem ownPtrD_lsOwn (p : Loc) (s : Option kd.meta.LabelSelector) :
    (ownPtrD (V := k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelector) kd.meta.LabelSelector.own
      p DFrac.discard s : IProp GF) ⊢ labels.lsOwn p (s.map selVOf) := by
  cases s with
  | none =>
    unfold ownPtrD
    iintro %h
    simp only [Option.map_none]
    unfold labels.lsOwn
    ipureintro; exact h
  | some s =>
    unfold ownPtrD
    iintro ⟨%x, Hp, Hown⟩
    simp only [Option.map_some, selVOf]
    unfold labels.lsOwn
    iunfold kd.meta.LabelSelector.own at Hown
    icases Hown with ⟨HML, HME⟩
    iunfold ownSliceD at HME
    icases HME with ⟨%vs, Hsl, Hall⟩
    ihave %hlen := BigSepL2.bigSepL2_length $$ Hall
    ihave Hreqs := lsReqs_of vs s.MatchExpressions' $$ Hall
    ihave Hml := ownMapD_lsml x.MatchLabels' s.MatchLabels' $$ HML
    iexists x.MatchLabels', x.MatchExpressions', vs
    isplitl [Hp]
    · iexact Hp
    isplitl [Hml]
    · iexact Hml
    isplitl [Hsl]
    · iexact Hsl
    isplitr
    · ipureintro; simp [hlen]
    iexact Hreqs

/-- **The DaemonSet's selector** (`ds.Spec.Selector`), read-only, holding `selOf d`. -/
theorem dsAt_sel (ds : Loc) (d : kd.apps.DaemonSet) :
    dsAt (GF := GF) ds DFrac.discard d ⊢
      ∃ ls : Loc, ds.[k8s_io.api.apps.v1.DaemonSet, go!"Spec"].[k8s_io.api.apps.v1.DaemonSetSpec,
        go!"Selector"] ↦□ ls ∗ labels.lsOwn ls (selOf d) := by
  unfold dsAt
  iintro ⟨%v, Hl, Hd⟩
  iStructNamed Hl
  iStructNamedPrefix Spec "S"
  iunfold kd.apps.DaemonSet.own at Hd
  icases Hd with ⟨-, -, DSpec, -⟩
  iunfold kd.apps.DaemonSetSpec.own at DSpec
  icases DSpec with ⟨DSel, -, -, -, -⟩
  iexists v.Spec'.Selector'
  isplitr [DSel]
  · iexact SSelector
  rw [selOf_eq]
  iapply ownPtrD_lsOwn
  iexact DSel

end lemmas

end dsctl
end EtcdGrove
end Perennial
