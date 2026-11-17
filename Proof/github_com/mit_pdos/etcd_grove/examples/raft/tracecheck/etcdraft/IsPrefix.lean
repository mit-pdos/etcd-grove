/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `IsPrefix`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsPrefix
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EntriesEqual

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

theorem IsPrefix.wp_proof (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG)) :
    IsPrefix.spec (GF := GF) (hG := hG) := by
  intro sl s tl t
  wp_start as ⟨#Hs, #Ht⟩
  ihave #Hs0 := Hs
  ihave #Ht0 := Ht
  iunfold logRO at Hs0 Ht0
  icases Hs0 with ⟨%es, #Hes, #Hse⟩
  icases Ht0 with ⟨%fs, #Hfs, #Htf⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hfl := ownSlice_len $$ Hfs
  ihave %Hfc := ownSlice_wf $$ Hfs
  ihave %Hsl := BigSepL2.bigSepL2_length $$ Hse
  ihave %Htl := BigSepL2.bigSepL2_length $$ Htf
  wp_auto
  have hsz : sint.Z sl.len = (s.length : Int) := by rw [← Hsl, Hel.1]; word
  have htz : sint.Z tl.len = (t.length : Int) := by rw [← Htl, Hfl.1]; word
  have h0 : sint.Z (W64 0) = 0 := rfl
  wp_if_destruct
  · try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z sl.len ∧
      sint.Z sl.len ≤ sint.Z tl.cap from ⟨by decide, by omega, by omega⟩))]
    try wp_auto
    ihave #Hsub := logRO_subslice tl t (W64 0) sl.len ⟨by decide, by omega, by omega⟩ $$ Ht
    wp_apply wp_EntriesEqual $$ [Hs Hsub]
    · iframe Hs Hsub
    iintro -
    try wp_auto
    have : isPrefix s t = decide (s = subslice 0 (sint.nat sl.len) t) := by
      unfold isPrefix
      have h1 : decide (s.length ≤ t.length) = true := decide_eq_true (by omega)
      have h2 : subslice 0 (sint.nat sl.len) t = t.take s.length := by
        rw [show sint.nat sl.len = s.length by word]
        simp [subslice]
      rw [h1, Bool.true_and, h2]
      by_cases h : t.take s.length = s
      · rw [h]; simp
      · simp [h, Ne.symm h]
    rw [this]
    iapply HΦ; ipureintro; trivial
  · try wp_auto
    have : isPrefix s t = false := by
      unfold isPrefix
      rw [decide_eq_false (by omega), Bool.false_and]
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
