/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): the proof of `SubSeq`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq

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

theorem SubSeq.wp_proof : SubSeq.spec (GF := GF) (hG := hG) := by
  intro sl s m n r
  wp_start as ⟨#Hs, %Hr⟩
  ihave #Hs0 := Hs
  iunfold logRO at Hs0
  icases Hs0 with ⟨%es, #Hes, #Hse⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hsl := BigSepL2.bigSepL2_length $$ Hse
  have hlen : sint.Z sl.len = (s.length : Int) := by rw [← Hsl, Hel.1]; word
  have h1 : sint.Z (W64 1) = 1 := rfl
  wp_auto
  wp_if_destruct
  · -- `m > n`: nil, the empty sequence
    have : r = [] := by
      unfold subSeq at Hr; rw [ite_eq_left (by omega)] at Hr; cases Hr; rfl
    subst this
    try wp_auto
    iapply HΦ
    iunfold logRO
    iexists []
    isplitr
    · iapply ownSlice_nil
    iapply BigSepL2.bigSepL2_nil.2
    iempintro
  · unfold subSeq at Hr
    rw [ite_eq_right (by omega)] at Hr
    split at Hr
    · cases Hr
    rename_i hmn
    cases Hr
    try wp_auto
    wp_if_destruct
    · exfalso; exact hmn (.inl (by omega))
    try wp_auto
    wp_if_destruct
    · exfalso; exact hmn (.inr (by omega))
    try wp_auto
    ihave %Hcap := ownSlice_wf $$ Hes
    have hm' : sint.Z (m - W64 1) = sint.Z m - 1 := by word
    have hb : 0 ≤ sint.Z (m - W64 1) ∧ sint.Z (m - W64 1) ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len := by
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (m - W64 1) ∧ sint.Z (m - W64 1) ≤ sint.Z n ∧
      sint.Z n ≤ sint.Z sl.cap from ⟨hb.1, hb.2.1, by omega⟩))]
    try wp_auto
    ihave #Hsub := logRO_subslice sl s (m - W64 1) n hb $$ Hs
    iapply HΦ
    have hl : subslice (sint.nat (m - W64 1)) (sint.nat n) s =
        List.take ((sint.Z n - sint.Z m + 1).toNat) (List.drop ((sint.Z m - 1).toNat) s) := by
      have e1 : sint.nat (m - W64 1) = (sint.Z m - 1).toNat := by
        rw [show sint.nat (m - W64 1) = (sint.Z (m - W64 1)).toNat from rfl, hm']
      have e2 : sint.nat n = (sint.Z n).toNat := rfl
      rw [e1, e2]
      simp only [subslice, List.drop_take]
      congr 1; omega
    rw [← hl]
    iexact Hsub

end proof

end AntCheck
end EtcdGrove
end Perennial
