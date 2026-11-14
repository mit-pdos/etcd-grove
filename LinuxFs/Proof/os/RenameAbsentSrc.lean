/-
The proof of `Spec/os/RenameAbsentSrc.lean`: the model's `LstatDir` of the target (a directory: the
`LinkError` at once), then its `EINTR` loop by Löb induction, each attempt a `CallBegin` and the
extension's `Rename` of the absent source (`wp_osRenameAbsentS`: a nonzero errno, no effect).
Lean-first.
-/
module

public import LinuxFs.Spec.os.RenameAbsentSrc
public import LinuxFs.Proof.os.Rename

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [syscall.Assumptions]

theorem os.Rename.wp_proofAbsentSrc : os.Rename.specAbsentSrc (GF := GF) (hG := hG) := by
  intro d bs bt j N R qd dqn h qc hbs hbt hN hN' hsrc
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn⟩
  imod osNames_next R j N _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  wp_apply wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_apply wp_osLstatDirS_mem R d bt j N (DFrac.own qd) dqn h t s0 qc hbt hN'
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %isDir %e %hd Hperm Hp Hn
  by_cases h1 : isDir = W64 1
  · rw [decide_eq_true h1]
    wp_auto
    wp_apply wp_linkError
    iintro %le
    iapply HΦ
    iframe
    ipureintro; exact ⟨fun hc => (by cases hc), Or.inr ⟨le, rfl⟩⟩
  rw [decide_eq_false h1]
  wp_auto
  iloeb as IH generalizing Hperm Hp Hn HΦ
  wp_apply +noauto wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t' %s1 %hs' Hk Hls
  iclear Hls
  ihave Hpp := (osPathS_frac R d qd.half qd.half j).1 $$ [Hp]
  · rw [Qp.half_add_half]; iexact Hp
  icases Hpp with ⟨Hp1, Hp2⟩
  wp_apply +noauto wp_osRenameAbsentS R d bs d bt j j N (DFrac.own qd.half) (DFrac.own qd.half) dqn h
    t' s1 qc hbs hbt hN hsrc CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp1 Hp2 Hn Hk
    as %e' %he' Hperm Hp1 Hp2 Hn
  ihave Hp := (osPathS_frac R d qd.half qd.half j).2 $$ [Hp1 Hp2]
  · iframe
  rw [Qp.half_add_half]
  wp_auto
  by_cases he4 : e' = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ Hperm Hp Hn HΦ
  rw [decide_eq_false (show e' ≠ W64 4 from he4)]
  wp_auto
  rw [decide_eq_false (show e' ≠ W64 0 from he')]
  wp_auto
  wp_apply wp_linkError
  iintro %le
  iapply HΦ
  iframe
  ipureintro; exact ⟨fun hc => (by cases hc), Or.inr ⟨le, rfl⟩⟩

end proof

end EtcdGrove
end Perennial
