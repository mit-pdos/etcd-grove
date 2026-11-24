/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): the proof of `At`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At

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

theorem At.wp_proof : At.spec (GF := GF) (hG := hG) := by
  intro sl l k x
  wp_start as ⟨#Hl, %Hr⟩
  iunfold logRO at Hl
  icases Hl with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  have hlz : sint.Z sl.len = (l.length : Int) := by rw [← Hll, Hel.1]; word
  unfold atE at Hr
  split at Hr
  · cases Hr
  rename_i hin
  have h1 : sint.Z (W64 1) = 1 := rfl
  wp_auto
  wp_if_destruct
  · exfalso; exact hin (.inl (by omega))
  try wp_auto
  wp_if_destruct
  · exfalso; exact hin (.inr (by omega))
  try wp_auto
  have hk : sint.Z (k - W64 1) = sint.Z k - 1 := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (k - W64 1) ∧
    sint.Z (k - W64 1) < sint.Z sl.len from by rw [hk]; constructor <;> omega))]
  obtain ⟨e, He⟩ : ∃ e, es[(sint.Z (k - W64 1)).toNat]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by rw [hk]; omega)⟩
  have Hx : l[(sint.Z (k - W64 1)).toNat]? = some x := by
    cases Hr
    rw [List.getElem!_eq_getElem?_getD, hk, List.getElem?_eq_getElem (by omega)]; rfl
  ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He Hx $$ Hle
  icases ownSlice_elem_acc _ e sl _ es (by rw [hk]; omega) He $$ Hes with ⟨He', -⟩
  wp_auto
  iapply HΦ
  iexact Hex

end proof

end AntCheck
end EtcdGrove
end Perennial
