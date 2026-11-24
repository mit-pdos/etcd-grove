/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Event.w`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__w
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

theorem Event.w.field {β : Type} {o : Option β} {x : β} (Hx : need o = .ok x) : o = some x := by
  cases o with
  | none => cases Hx
  | some a => cases Hx; rfl

theorem Event.w.rel {α β : Type} {has bit : w32} {rel : α → β → Prop} {g : α} {o : Option β}
    {x : β} (Hf : fieldRel has bit rel g o) (Hx : o = some x) : hasBit has bit ∧ rel g x := by
  subst Hx; exact Hf

theorem Event.w.wp_proof (wp_need : Event.need.spec (GF := GF) (hG := hG)) :
    Event.w.spec (GF := GF) (hG := hG) := by
  intro p ev x
  wp_start as ⟨#Hev, %Hx⟩
  ihave #Hev' := Hev
  iunfold eventRO at Hev'
  icases Hev' with ⟨%g, #Hp, %Hf, #HR0, #HR1, #HR2, #HR3, #HR4⟩
  have ho := Event.w.field (o := ev.w) Hx
  obtain ⟨hb, hr⟩ := Event.w.rel Hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho
  iStructNamed Hp
  wp_auto
  wp_apply wp_need p ev (W32 131072) $$ [Hev]
  · iframe Hev; ipureintro; simp [Event.hasF, ho, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries,
      fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]
  iapply HΦ
  ipureintro; exact hr

end proof

end AntCheck
end EtcdGrove
end Perennial
