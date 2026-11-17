/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `SubSeq`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.SubSeq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section cap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A slice's elements, its capacity cut to its length (`s[lo:hi:hi]`). Perennial's slice laws
have no full-slice counterpart of `ownSlice_slice`; this is the step from one (a candidate for
Perennial, `notes/perennial-changes.md`). -/
theorem ownSlice_cap_to_len {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (p : Loc) (l c : w64) (dq : DFrac) (vs : List V) :
    (slice.mk p l c ↦*{dq} vs : IProp GF) ⊢ slice.mk p l l ↦*{dq} vs := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, %Hc⟩)
  · ileft; ipureintro
    obtain ⟨H1, H2⟩ := H
    refine ⟨?_, H2⟩
    injection H1 with h1 h2 h3
    rw [h1, h2]; rfl
  · iright
    iframe Hsl
    ipureintro; simp only; exact Int.le_refl _

end cap

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem SubSeq.wp_proof : SubSeq.spec (GF := GF) (hG := hG) := by
  intro sl s m n r
  wp_start as ⟨#Hs, %Hr⟩
  ihave #Hs0 := Hs
  iunfold logRO at Hs0
  icases Hs0 with ⟨%es, #Hes, #Hse⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hsl := BigSepL2.bigSepL2_length $$ Hse
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
    have hm1 : ¬ sint.Z m < sint.Z (W64 1) := by
      rw [show sint.Z (W64 1) = 1 from rfl]; omega
    rw [decide_eq_false hm1]
    try wp_auto
    have hns : ¬ sint.Z sl.len < sint.Z n := by
      have : sint.Z sl.len = (s.length : Int) := by rw [← Hsl, Hel.1]; word
      omega
    rw [decide_eq_false hns]
    try wp_auto
    ihave %Hcap := ownSlice_wf $$ Hes
    have hlen : sint.Z sl.len = (s.length : Int) := by rw [← Hsl, Hel.1]; word
    have hm' : sint.Z (m - W64 1) = sint.Z m - 1 := by
      rw [show sint.Z (W64 1) = 1 from rfl] at hm1; word
    have hb : 0 ≤ sint.Z (m - W64 1) ∧ sint.Z (m - W64 1) ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len := by
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (m - W64 1) ∧ sint.Z (m - W64 1) ≤ sint.Z n ∧
      sint.Z n ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.cap from ⟨hb.1, hb.2.1, Int.le_refl _, by omega⟩))]
    try wp_auto
    ihave #Hsub := logRO_subslice sl s (m - W64 1) n hb $$ Hs
    iapply HΦ
    have hl : subslice (sint.nat (m - W64 1)) (sint.nat n) s =
        List.take ((sint.Z n).toNat - (sint.Z m).toNat + 1) (List.drop ((sint.Z m).toNat - 1) s) := by
      have e1 : sint.nat (m - W64 1) = (sint.Z m).toNat - 1 := by
        rw [show sint.nat (m - W64 1) = (sint.Z (m - W64 1)).toNat from rfl, hm']; omega
      have e2 : sint.nat n = (sint.Z n).toNat := rfl
      rw [e1, e2]
      simp only [subslice, List.drop_take]
      congr 1; omega
    rw [← hl]
    iunfold logRO at Hsub
    iunfold logRO
    icases Hsub with ⟨%fs, #Hfs, #Hf⟩
    iexists fs
    isplitr
    · simp only [slice.fullSlice, slice.slice]
      iapply ownSlice_cap_to_len
      iexact Hfs
    iexact Hf

end proof

end Etcdraft
end EtcdGrove
end Perennial
