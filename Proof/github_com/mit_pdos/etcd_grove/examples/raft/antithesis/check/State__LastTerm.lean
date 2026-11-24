/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.LastTerm`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__LastTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermAt
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

/-- `s.Log[k]`. -/
theorem State.LastTerm_logsRO_at (sl : GoSlice) (ls : List (List Entry)) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k < ls.length) :
    logsRO (GF := GF) sl ls ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ logRO v ls[sint.nat k]! := by
  iintro #H
  iunfold logsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g l => logRO (GF := GF) g l) sl gs ls k hk
  iframe Hgs Hb

theorem State.LastTerm.wp_proof (wp_TermAt : TermAt.spec (GF := GF) (hG := hG)) :
    State.LastTerm.spec (GF := GF) (hG := hG) := by
  intro p s i
  wp_start as ⟨#Hs, %Hi⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases State.LastTerm_logsRO_at g.Log' s.log i ⟨Hi.1, by rw [HWf.len_log]; exact Hi.2⟩ $$ HLog with ⟨%v, #Hva, #Hv⟩
  wp_auto
  wp_apply wp_load_at _ _ v Hi.1 $$ [Hva]
  · iexact Hva
  try wp_auto
  wp_apply wp_load_at _ _ v Hi.1 $$ [Hva]
  · iexact Hva
  try wp_auto
  ihave #Hv' := Hv
  iunfold logRO at Hv'
  icases Hv' with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  wp_apply wp_TermAt v _ v.len $$ [Hv] as %r %Hr
  · iexact Hv
  try wp_auto
  iapply HΦ
  ipureintro
  rw [Hr]
  unfold State.lastTerm
  congr 1
  rw [← Hll, Hel.1]; word

end proof

end AntCheck
end EtcdGrove
end Perennial
