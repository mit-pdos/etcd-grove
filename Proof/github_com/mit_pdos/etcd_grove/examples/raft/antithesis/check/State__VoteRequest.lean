/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.VoteRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__VoteRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__LastTerm
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
theorem State.VoteRequest_logsRO_at (sl : GoSlice) (ls : List (List Entry)) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k < ls.length) :
    logsRO (GF := GF) sl ls ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ logRO v ls[sint.nat k]! := by
  iintro #H
  iunfold logsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g l => logRO (GF := GF) g l) sl gs ls k hk
  iframe Hgs Hb

/-- A log's length. -/
theorem State.VoteRequest_logRO_len (sl : GoSlice) (l : List Entry) :
    logRO (GF := GF) sl l ⊢ ⌜sint.Z sl.len = (l.length : Int)⌝ := by
  iintro #H
  iunfold logRO at H
  icases H with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  ipureintro
  rw [← Hll, Hel.1]; word

theorem State.VoteRequest.wp_proof (wp_LastTerm : State.LastTerm.spec (GF := GF) (hG := hG)) :
    State.VoteRequest.spec (GF := GF) (hG := hG) := by
  intro p s i t
  wp_start as ⟨#Hs, %Hi0, %Hi1⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hc, #Hsv, #Hiv, %Hb⟩
  iStructNamed Hc
  iunfold strsRO at Hsv
  icases State.VoteRequest_logsRO_at g.Log' s.log i ⟨Hi0, by rw [HWf.len_log]; exact Hi1⟩ $$ HLog with ⟨%v, #Hva, #Hv⟩
  ihave %Hvl := State.VoteRequest_logRO_len v _ $$ Hv
  have hsv : s.cfg.server[sint.nat i]? = some s.cfg.server[sint.nat i]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by word)]; rfl
  wp_auto
  wp_apply wp_load_index _ i _ _ Hi0 hsv $$ [Hsv]
  · iexact Hsv
  try wp_auto
  wp_apply wp_load_at _ _ v Hi0 $$ [Hva]
  · iexact Hva
  try wp_auto
  wp_apply wp_LastTerm p s i $$ [Hs] as %w %Hw
  · iframe Hs; ipureintro; exact ⟨Hi0, Hi1⟩
  try wp_auto
  iapply HΦ
  ipureintro
  unfold State.voteRequest factRel
  simp only
  exact ⟨trivial, trivial, trivial, trivial, Hvl, Hw, rfl⟩

end proof

end AntCheck
end EtcdGrove
end Perennial
