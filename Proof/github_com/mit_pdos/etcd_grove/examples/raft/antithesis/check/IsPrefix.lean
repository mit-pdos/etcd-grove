/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): the proof of `IsPrefix`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsPrefix
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual

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

theorem IsPrefix.wp_proof (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG)) :
    IsPrefix.spec (GF := GF) (hG := hG) := by
  intro al a bl b r
  wp_start as ⟨#Ha, #Hb, %Hr⟩
  ihave #Ha0 := Ha
  ihave #Hb0 := Hb
  iunfold logRO at Ha0 Hb0
  icases Ha0 with ⟨%es, #Hes, #Hae⟩
  icases Hb0 with ⟨%fs, #Hfs, #Hbf⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hfl := ownSlice_len $$ Hfs
  ihave %Hael := BigSepL2.bigSepL2_length $$ Hae
  ihave %Hbfl := BigSepL2.bigSepL2_length $$ Hbf
  have hla : sint.Z al.len = (a.length : Int) := by rw [← Hael, Hel.1]; word
  have hlb : sint.Z bl.len = (b.length : Int) := by rw [← Hbfl, Hfl.1]; word
  unfold isPrefix at Hr
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left (by omega)] at Hr
    cases hs : subSeq b 1 a.length with
    | error _ => rw [hs] at Hr; cases Hr
    | ok u =>
    rw [hs] at Hr
    try wp_auto
    wp_apply wp_SubSeq _ _ _ _ u $$ [Hb] as %ul #Hu
    · iframe Hb; ipureintro
      rw [show sint.Z (W64 1) = 1 from rfl, hla]; exact hs
    try wp_auto
    wp_apply wp_EntriesEqual _ _ _ _ r $$ [Ha Hu]
    · iframe Ha Hu; ipureintro; exact Hr
    try wp_auto
    iapply HΦ; ipureintro; trivial
  · try wp_auto
    rw [ite_eq_right (by omega)] at Hr
    cases Hr
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
