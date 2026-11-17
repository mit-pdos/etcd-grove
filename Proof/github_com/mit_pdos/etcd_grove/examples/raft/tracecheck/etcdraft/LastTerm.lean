/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `LastTerm`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.LastTerm

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

theorem LastTerm.wp_proof : LastTerm.spec (GF := GF) (hG := hG) := by
  intro sl l
  wp_start as #Hl
  iunfold logRO at Hl
  icases Hl with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  wp_auto
  wp_if_destruct
  · try wp_auto
    have : l = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← Hll, Hel.1, Hif]; rfl
    subst this
    iapply HΦ; ipureintro; rfl
  · try wp_auto
    have hpos : 0 < es.length := by
      rw [Hel.1]; have : sint.Z sl.len ≠ 0 := fun h => Hif (by word); word
    have hk : sint.Z (sl.len - W64 1) = (es.length : Int) - 1 := by rw [Hel.1]; word
    have hlz : sint.Z sl.len = (es.length : Int) := by rw [Hel.1]; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (sl.len - W64 1) ∧
      sint.Z (sl.len - W64 1) < sint.Z sl.len from by rw [hk, hlz]; constructor <;> omega))]
    obtain ⟨e, He⟩ : ∃ e, es[(sint.Z (sl.len - W64 1)).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [hk]; omega)⟩
    obtain ⟨x, Hx⟩ : ∃ x, l[(sint.Z (sl.len - W64 1)).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hk, ← Hll]; omega)⟩
    ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He Hx $$ Hle
    iunfold entryRO at Hex
    icases Hex with ⟨%Hex, -⟩
    icases ownSlice_elem_acc _ e sl _ es (by rw [hk]; omega) He $$ Hes with ⟨He', -⟩
    icases typedPointsto_split _ _ _ $$ He' with Hef
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hef
    wp_auto
    iapply HΦ
    ipureintro
    rw [Hex.1]
    unfold lastTerm
    rw [List.getLast?_eq_getElem?, show l.length - 1 = (sint.Z (sl.len - W64 1)).toNat by rw [hk, ← Hll]; omega,
      Hx]

end proof

end Etcdraft
end EtcdGrove
end Perennial
