/-
# A node at term `0` has an empty log (2026-10-29, stage U4 of `notes/raft-unified-plan.md`)

Every recorded entry has a term of at least `1` (`isEntryR_term_one`: a leader's term is a
campaign's, nonzero by `CampOk.term_nz`; a boot entry's is `1`), and a node's full log has no term
above the node's (`TermsLe`). So a node at term `0` has an empty full log: its boundary is the
initial one and its log suffix empty (`ownLogGhost_term0`), and it grants every pre-vote request
(`plogUpToDate` at `base0` holds of every candidate). What `raft.Step`'s pre-vote case needs at term
`0` (a rejection there would be sent at term `0`, which `send` refuses) without the bootstrap-log
premise (`ownLogGhost_boot`'s `γ.reBoot ≠ [] → 1 ≤ term`) that excluded clusters started empty.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.ReadIndex

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **A record's term is at least `1`**, in every cluster: a leader's term is its campaign's,
nonzero; a boot entry's is `1`. -/
theorem isEntryR_term_one (γ : RaftNames) (e : EntryM) (pt : w64) :
    ⊢ isEntryR (GF := GF) γ e pt -∗ ⌜1 ≤ uint.Z e.Term'⌝ := by
  unfold isEntryR
  iintro (⟨%ldr, %_, %_, %_, %_, -, -, #Hc, -, -, -⟩ | ⟨%Hb, -⟩)
  · icases isCamp_ok γ ldr e.Term' _ $$ Hc with %Hok
    have Hnz := Hok.term_nz
    ipureintro
    have h0 := uint_Z_nonneg e.Term'
    have h1 : uint.Z e.Term' ≠ 0 := fun h => Hnz (by word)
    omega
  · ipureintro
    obtain ⟨-, -, Ht, -⟩ := Hb
    rw [Ht]; word

/-- **At term `0` a node's log is empty**: its boundary is the initial one, its suffix empty. -/
theorem ownLogGhost_term0 (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      ⌜s.term = W64 0 → plogLast s.base s.log = base0⌝ := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  have ⟨Hf, Hw, Htle⟩ := Hfull
  have HwF : PlogWf base0 (fp ++ s.log) := full_wf _ _ _ Hf Hw
  ihave #HrF := logRecs_full γ s.base fp s.log Hf $$ Hfrecs Hrecs
  rw [← full_last _ _ _ Hf]
  cases hF : (fp ++ s.log).getLast? with
  | none =>
    ipureintro; intro _
    unfold plogLast; rw [hF]
  | some e =>
    have hl := List.getLast?_eq_getElem? (l := fp ++ s.log)
    rw [hF] at hl
    have hlen : 0 < (fp ++ s.log).length := by
      cases h : (fp ++ s.log) with
      | nil => rw [h] at hF; cases hF
      | cons _ _ => simp
    have hk : (fp ++ s.log)[(fp ++ s.log).length - 1]? = some e := hl.symm
    have hidx := HwF _ e hk
    rw [base0_index] at hidx
    have hr := (word.unsigned_range e.Index').2
    icases logRecs_lookup γ (fp ++ s.log) _ e hk (by push_cast at hidx ⊢; omega) $$ HrF
      with ⟨%pt, -, #Hr⟩
    icases isEntryR_term_one γ e pt $$ Hr with %Hp
    ipureintro
    intro hT
    exfalso
    have Hat : plogTermAt base0 (fp ++ s.log) e.Index' = some e.Term' :=
      plogTermAt_lookup base0 _ e.Index' _ e hk (by rw [base0_index]; omega)
    have := (Htle e.Index' e.Term' Hat).1
    rw [hT] at this
    rw [show uint.Z (W64 0) = 0 from rfl] at this
    omega

/-- At the initial boundary with an empty suffix, every candidate is up to date. -/
theorem plogUpToDate_base0 (b : entryID) (es : List EntryM) (x : entryID) :
    plogLast b es = base0 → plogUpToDate b es x = true := by
  intro H
  unfold plogUpToDate
  rw [H]
  simp only [base0]
  apply decide_eq_true
  by_cases h : x.term' = W64 0
  · apply Or.inr; exact ⟨h, by have := uint_Z_nonneg x.index'; rw [show uint.Z (W64 0) = 0 from rfl]; omega⟩
  · apply Or.inl
    have := uint_Z_nonneg x.term'
    rw [show uint.Z (W64 0) = 0 from rfl]
    have h1 : uint.Z x.term' ≠ 0 := fun h' => h (by word)
    omega

end ghost

end EtcdGrove
end Perennial
