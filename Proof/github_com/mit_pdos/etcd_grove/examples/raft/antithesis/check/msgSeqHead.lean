/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `msgSeqHead`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.msgSeqHead
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

theorem msgSeqHead.wp_proof : msgSeqHead.spec (GF := GF) (hG := hG) := by
  intro sl ms m
  wp_start as ⟨#Hl, %Hr⟩
  iunfold msgsRO at Hl
  icases Hl with ⟨%gs, #Hgs, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hgs
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  obtain ⟨rest, rfl⟩ : ∃ rest, ms = m :: rest := by
    cases ms with
    | nil => cases Hr
    | cons a rest => cases Hr; exact ⟨rest, rfl⟩
  obtain ⟨g, gs', rfl⟩ : ∃ g gs', gs = g :: gs' := by
    cases gs with
    | nil => simp at Hll
    | cons g gs' => exact ⟨g, gs', rfl⟩
  ihave #Hg := BigSepL2.bigSepL2_lookup (Φ := fun _ g m => msgRO (GF := GF) g m)
    (i := 0) rfl rfl $$ Hle
  wp_auto
  wp_if_destruct
  · exfalso; have h1 := Hel.1; have h3 : sint.nat sl.len = 0 := by rw [Hif]; rfl
    simp only [List.length_cons] at h1; omega
  try wp_auto
  wp_apply wp_load_index sl (W64 0) (g :: gs') g (by decide) rfl $$ [Hgs]
  · iexact Hgs
  iapply HΦ
  iexact Hg

end proof

end AntCheck
end EtcdGrove
end Perennial
