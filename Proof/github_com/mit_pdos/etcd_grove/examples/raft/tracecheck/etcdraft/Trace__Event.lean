/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__Event`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__Event

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

theorem Trace.Event.wp_proof : Trace.Event.spec (GF := GF) (hG := hG) := by
  intro t tr l
  wp_start as ⟨#Ht, %Hl1, %Hl2⟩
  open_trace
  wp_auto
  have hi : sint.Z (l - W64 1) = sint.Z l - 1 := by word
  have hb : 0 ≤ sint.Z (l - W64 1) ∧ sint.Z (l - W64 1) < sint.Z gt.lines'.len := by
    rw [hi, ← hlenZ]; constructor <;> omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  have hn1 : 1 ≤ sint.nat l := by word
  have hn2 : sint.nat l ≤ tr.len := by word
  have hx := Trace.line_eq tr (sint.nat l) hn1 hn2
  have hk : (sint.Z (l - W64 1)).toNat = sint.nat l - 1 := by rw [hi]; word
  obtain ⟨x, Hx⟩ : ∃ x, lns[(sint.Z (l - W64 1)).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hk, Hll]; unfold Trace.len at hn2; omega)⟩
  rw [hk] at Hx
  ihave #Hxy := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) Hx hx $$ Hl
  rw [← hk] at Hx
  icases ownSlice_elem_acc _ x _ _ lns hb.1 Hx $$ Hlns with ⟨#Hxe, -⟩
  icases typedPointsto_split _ _ _ $$ Hxe with Hxf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hxf with ⟨#X1, -⟩
  iunfold lineRO at Hxy
  icases Hxy with ⟨⟨%ge, #Hge, #Hger⟩, -⟩
  wp_auto
  iapply HΦ
  iexists ge
  isplitr
  · iexact Hge
  iexact Hger

end proof

end Etcdraft
end EtcdGrove
end Perennial
