/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): the proof of `TermAt`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem TermAt.wp_proof : TermAt.spec (GF := GF) (hG := hG) := by
  intro sl l k
  wp_start as #Hl
  iunfold logRO at Hl
  icases Hl with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  have hlz : sint.Z sl.len = (l.length : Int) := by rw [← Hll, Hel.1]; word
  wp_auto
  wp_if_destruct
  · try wp_auto
    wp_if_destruct
    · try wp_auto
      have h0 : sint.Z (W64 0) = 0 := rfl
      have hk : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (k - W64 1) ∧
        sint.Z (k - W64 1) < sint.Z sl.len from by rw [hk]; constructor <;> omega))]
      obtain ⟨e, He⟩ : ∃ e, es[(sint.Z (k - W64 1)).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [hk]; omega)⟩
      obtain ⟨x, Hx⟩ : ∃ x, l[(sint.Z (k - W64 1)).toNat]? = some x :=
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
      unfold termAt
      rw [ite_eq_left (by omega), show (sint.Z k - 1).toNat = (sint.Z (k - W64 1)).toNat by rw [hk],
        List.getElem!_eq_getElem?_getD, Hx]
      rfl
    · try wp_auto
      iapply HΦ; ipureintro
      unfold termAt; rw [ite_eq_right (by omega)]; rfl
  · try wp_auto
    iapply HΦ; ipureintro
    unfold termAt; rw [ite_eq_right (by rw [show sint.Z (W64 0) = 0 from rfl] at Hif; omega)]; rfl

end proof

end AntCheck
end EtcdGrove
end Perennial
