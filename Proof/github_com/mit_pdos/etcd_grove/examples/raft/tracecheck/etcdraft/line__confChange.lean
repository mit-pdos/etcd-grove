/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `line__confChange`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__confChange
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.parseID

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem line.confChange.wp_proof (wp_parseID : parseID.spec (GF := GF) (hG := hG)) :
    line.confChange.spec (GF := GF) (hG := hG) := by
  intro q x
  wp_start as #Hlp
  ihave HΦ' : (∀ (a : GoString) (j : w64) (ok : Bool), ⌜match x.confChange with
       | none => ok = false
       | some (act, n) => ok = true ∧ strRel a act ∧ uint.nat j = n⌝ -∗ Φ (PairV (PairV #a #j) #ok)) $$ [HΦ]
  · iintro %a %j %ok %h; iapply HΦ; ipureintro; exact h
  open_lineP
  wp_auto
  iunfold propsRO at Heprop
  cases hp : x.ev.prop with
  | none =>
    icases Heprop with %Hnull
    rw [Hnull]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.confChange, hp]
  | some pr =>
  icases Heprop with ⟨%gp, #Hgp, #Hcc⟩
  ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
  rw [decide_eq_false Hgpnn]
  icases typedPointsto_split _ _ _ $$ Hgp with Hgpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hgpf with ⟨#GP1, -⟩
  wp_auto
  cases hcc : pr.cc with
  | none =>
    icases Hcc with %Hnull
    rw [Hnull]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.confChange, hp, hcc]
  | some cc =>
  iunfold confChangeRO at Hcc
  icases Hcc with ⟨%gcc, #Hgcc, #Hch, -⟩
  ihave %Hgccnn := typedPointsto_not_null _ _ _ $$ Hgcc
  rw [decide_eq_false Hgccnn]
  icases typedPointsto_split _ _ _ $$ Hgcc with Hgccf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hgccf with ⟨#CC1, -⟩
  wp_auto
  iunfold optSliceRO at Hch
  cases hch : cc.changes with
  | none =>
    icases Hch with %Hnull
    rw [Hnull]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.confChange, hp, hcc, hch]
  | some xs =>
  icases Hch with ⟨%csl, %vs, #Hcsl, #Hvs, %Hrel⟩
  ihave %Hcnn := typedPointsto_not_null _ _ _ $$ Hcsl
  rw [decide_eq_false Hcnn]
  ihave %Hvl := ownSlice_len $$ Hvs
  have Hll : vs.length = xs.length := Hrel.length_eq
  wp_auto
  have hlz : sint.Z csl.len = (xs.length : Int) := by rw [← Hll, Hvl.1]; word
  by_cases h1 : xs.length = 1
  rotate_left
  · rw [decide_eq_false (show ¬ csl.len = W64 1 by
      intro e; apply h1; rw [e] at hlz; have : sint.Z (W64 1) = 1 := rfl; omega)]
    simp only [Bool.not_false]
    wp_auto
    iapply HΦ'; ipureintro
    have : x.confChange = none := by
      unfold Line.confChange; rw [hp]; simp only [Option.bind_some, hcc, hch]
      match xs, h1 with
      | [], _ => rfl
      | [_], h => exact absurd rfl h
      | _ :: _ :: _, _ => rfl
    rw [this]
  rw [decide_eq_true (show csl.len = W64 1 by
    have : sint.Z csl.len = sint.Z (W64 1) := by rw [hlz, h1]; rfl
    exact (sint_eq_iff _ _ _ _ rfl rfl).2 this)]
  simp only [Bool.not_true]
  wp_auto
  obtain ⟨c, rfl⟩ : ∃ c, xs = [c] := List.length_eq_one_iff.1 h1
  obtain ⟨gc, Hgc⟩ : ∃ gc, vs[0]? = some gc := ⟨_, List.getElem?_eq_getElem (by rw [Hll]; simp)⟩
  have hgc : changeRel gc c := by
    cases Hrel with
    | cons hr _ => simp at Hgc; subst Hgc; exact hr
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z csl.len :=
    ⟨by decide, by rw [hlz, show sint.Z (W64 0) = 0 from rfl]; simp⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  wp_apply wp_load_slice_index csl (sint.Z (W64 0)) vs DFrac.discard gc (by decide) $$ [Hvs] as -
  · iframe Hvs; ipureintro; exact Hgc
  try wp_auto
  wp_apply wp_parseID gc.NID' c.nid $$ [] as %j %ok %Hj
  · ipureintro; exact hgc.1
  cases hpi : parseID c.nid with
  | none =>
    rw [hpi] at Hj; subst Hj
    wp_auto
    iapply HΦ'; ipureintro
    simp [Line.confChange, hp, hcc, hch, hpi]
  | some n =>
    rw [hpi] at Hj; obtain ⟨rfl, hj⟩ := Hj
    wp_auto
    iapply HΦ'; ipureintro
    simp only [Line.confChange, hp, hcc, hch, Option.bind_some, hpi, Option.map_some]
    exact ⟨by trivial, hgc.2, hj⟩

end proof

end Etcdraft
end EtcdGrove
end Perennial
