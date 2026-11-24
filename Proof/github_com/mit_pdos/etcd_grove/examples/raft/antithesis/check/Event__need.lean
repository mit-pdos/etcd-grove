/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Event.need`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__need

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

theorem Event.need.relIff {α β : Type} {has bit : w32} {rel : α → β → Prop} {g : α} {o : Option β}
    (Hf : fieldRel has bit rel g o) : hasBit has bit ↔ o.isSome := by
  cases o with
  | none => simpa [fieldRel] using Hf
  | some a => simpa [fieldRel] using Hf.1

theorem Event.need.roIff {α β : Type} {has bit : w32} {rep : α → β → IProp GF} {g : α} {o : Option β} :
    fieldRO has bit rep g o ⊢ ⌜hasBit has bit ↔ o.isSome⌝ := by
  cases o with
  | none => iintro H; iunfold fieldRO at H; icases H with %H; ipureintro; simpa using H
  | some a => iintro H; iunfold fieldRO at H; icases H with ⟨%H, -⟩; ipureintro; simpa using H

/-- `ev.hasF f = some b` means the bit `f` of the Go `Has` is set iff `b`. -/
theorem Event.need.bit (ev : Event) (h : w32) (f : w32) (b : Bool)
    (HB : hasBit h fB ↔ ev.b = true) (HA : hasBit h fA ↔ ev.a = true)
    (H1 : hasBit h fBy ↔ ev.byE.isSome) (H2 : hasBit h fRole ↔ ev.role.isSome)
    (H3 : hasBit h fTerm ↔ ev.term.isSome) (H4 : hasBit h fVote ↔ ev.vote.isSome)
    (H5 : hasBit h fCommit ↔ ev.commit.isSome) (H6 : hasBit h fFirst ↔ ev.first.isSome)
    (H7 : hasBit h fEntries ↔ ev.entries.isSome) (H8 : hasBit h fLastIndex ↔ ev.lastIndex.isSome)
    (H9 : hasBit h fLastTerm ↔ ev.lastTerm.isSome) (H10 : hasBit h fApplied ↔ ev.applied.isSome)
    (H11 : hasBit h fVoters ↔ ev.voters.isSome) (H12 : hasBit h fOutgoing ↔ ev.outgoing.isSome)
    (H13 : hasBit h fSnap ↔ ev.snap.isSome) (H14 : hasBit h fMsg ↔ ev.msg.isSome)
    (H15 : hasBit h fCause ↔ ev.cause.isSome) (H16 : hasBit h fW ↔ ev.w.isSome)
    (H17 : hasBit h fMore ↔ ev.more.isSome) (H18 : hasBit h fIndex ↔ ev.index.isSome)
    (H19 : hasBit h fCtx ↔ ev.ctx.isSome)
    (Hf : ev.hasF f = some b) : hasBit h f ↔ b = true := by
  unfold Event.hasF at Hf
  by_cases c0 : f = fBy
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c0)] at Hf; subst c0; cases Hf; exact H1
  rw [ite_eq_right_of_eq_false _ _ (eq_false c0)] at Hf
  by_cases c1 : f = fRole
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c1)] at Hf; subst c1; cases Hf; exact H2
  rw [ite_eq_right_of_eq_false _ _ (eq_false c1)] at Hf
  by_cases c2 : f = fTerm
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c2)] at Hf; subst c2; cases Hf; exact H3
  rw [ite_eq_right_of_eq_false _ _ (eq_false c2)] at Hf
  by_cases c3 : f = fVote
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c3)] at Hf; subst c3; cases Hf; exact H4
  rw [ite_eq_right_of_eq_false _ _ (eq_false c3)] at Hf
  by_cases c4 : f = fCommit
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c4)] at Hf; subst c4; cases Hf; exact H5
  rw [ite_eq_right_of_eq_false _ _ (eq_false c4)] at Hf
  by_cases c5 : f = fFirst
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c5)] at Hf; subst c5; cases Hf; exact H6
  rw [ite_eq_right_of_eq_false _ _ (eq_false c5)] at Hf
  by_cases c6 : f = fEntries
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c6)] at Hf; subst c6; cases Hf; exact H7
  rw [ite_eq_right_of_eq_false _ _ (eq_false c6)] at Hf
  by_cases c7 : f = fLastIndex
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c7)] at Hf; subst c7; cases Hf; exact H8
  rw [ite_eq_right_of_eq_false _ _ (eq_false c7)] at Hf
  by_cases c8 : f = fLastTerm
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c8)] at Hf; subst c8; cases Hf; exact H9
  rw [ite_eq_right_of_eq_false _ _ (eq_false c8)] at Hf
  by_cases c9 : f = fApplied
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c9)] at Hf; subst c9; cases Hf; exact H10
  rw [ite_eq_right_of_eq_false _ _ (eq_false c9)] at Hf
  by_cases c10 : f = fVoters
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c10)] at Hf; subst c10; cases Hf; exact H11
  rw [ite_eq_right_of_eq_false _ _ (eq_false c10)] at Hf
  by_cases c11 : f = fOutgoing
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c11)] at Hf; subst c11; cases Hf; exact H12
  rw [ite_eq_right_of_eq_false _ _ (eq_false c11)] at Hf
  by_cases c12 : f = fSnap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c12)] at Hf; subst c12; cases Hf; exact H13
  rw [ite_eq_right_of_eq_false _ _ (eq_false c12)] at Hf
  by_cases c13 : f = fMsg
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c13)] at Hf; subst c13; cases Hf; exact H14
  rw [ite_eq_right_of_eq_false _ _ (eq_false c13)] at Hf
  by_cases c14 : f = fCause
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c14)] at Hf; subst c14; cases Hf; exact H15
  rw [ite_eq_right_of_eq_false _ _ (eq_false c14)] at Hf
  by_cases c15 : f = fB
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c15)] at Hf; subst c15; cases Hf; exact HB
  rw [ite_eq_right_of_eq_false _ _ (eq_false c15)] at Hf
  by_cases c16 : f = fA
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c16)] at Hf; subst c16; cases Hf; exact HA
  rw [ite_eq_right_of_eq_false _ _ (eq_false c16)] at Hf
  by_cases c17 : f = fW
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c17)] at Hf; subst c17; cases Hf; exact H16
  rw [ite_eq_right_of_eq_false _ _ (eq_false c17)] at Hf
  by_cases c18 : f = fMore
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c18)] at Hf; subst c18; cases Hf; exact H17
  rw [ite_eq_right_of_eq_false _ _ (eq_false c18)] at Hf
  by_cases c19 : f = fIndex
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c19)] at Hf; subst c19; cases Hf; exact H18
  rw [ite_eq_right_of_eq_false _ _ (eq_false c19)] at Hf
  by_cases c20 : f = fCtx
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c20)] at Hf; subst c20; cases Hf; exact H19
  rw [ite_eq_right_of_eq_false _ _ (eq_false c20)] at Hf
  cases Hf

/-- The facts `Event.need.bit` takes, from a report's representation. -/
theorem Event.need.facts (p : Loc) (ev : Event) :
    eventRO (GF := GF) p ev ⊢ ∃ g : G.Event, p ↦□ g ∗ ⌜∀ f b, ev.hasF f = some b → (hasBit g.Has' f ↔ b = true)⌝ := by
  iunfold eventRO
  iintro ⟨%g, #Hp, %Hf, #HR0, #HR1, #HR2, #HR3, #HR4⟩
  ihave %H7 := Event.need.roIff $$ HR0
  ihave %H11 := Event.need.roIff $$ HR1
  ihave %H12 := Event.need.roIff $$ HR2
  ihave %H14 := Event.need.roIff $$ HR3
  ihave %H15 := Event.need.roIff $$ HR4
  iexists g
  iframe Hp
  ipureintro
  obtain ⟨-, -, -, HB, HA, H1, H2, H3, H4, H5, H6, H8, H9, H10, H13, H16, H17, H18, H19⟩ := Hf
  intro f b Hfb
  exact Event.need.bit ev g.Has' f b HB HA (Event.need.relIff H1) (Event.need.relIff H2) (Event.need.relIff H3)
    (Event.need.relIff H4) (Event.need.relIff H5) (Event.need.relIff H6) H7 (Event.need.relIff H8) (Event.need.relIff H9)
    (Event.need.relIff H10) H11 H12 (Event.need.relIff H13) H14 H15 (Event.need.relIff H16) (Event.need.relIff H17)
    (Event.need.relIff H18) (Event.need.relIff H19) Hfb

theorem Event.need.wp_proof : Event.need.spec (GF := GF) (hG := hG) := by
  intro p ev f
  wp_start as ⟨#Hev, %Hf⟩
  ihave ⟨%g, #Hp, %Hbit⟩ := Event.need.facts p ev $$ Hev
  have hb := (Hbit f true Hf).2 rfl
  iStructNamed Hp
  wp_auto
  wp_if_destruct
  · exact absurd (by assumption) hb
  iapply HΦ
  ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
