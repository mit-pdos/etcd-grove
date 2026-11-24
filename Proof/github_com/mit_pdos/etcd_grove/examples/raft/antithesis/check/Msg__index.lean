/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Msg.index`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__need

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

theorem Msg.index.field {β : Type} {o : Option β} {x : β} (Hx : need o = .ok x) : o = some x := by
  cases o with
  | none => cases Hx
  | some a => cases Hx; rfl

theorem Msg.index.rel {α β : Type} {has bit : w32} {rel : α → β → Prop} {g : α} {o : Option β}
    {x : β} (Hf : fieldRel has bit rel g o) (Hx : o = some x) : hasBit has bit ∧ rel g x := by
  subst Hx; exact Hf

theorem Msg.index.wp_proof (wp_need : Msg.need.spec (GF := GF) (hG := hG)) :
    Msg.index.spec (GF := GF) (hG := hG) := by
  intro g m x
  wp_start as ⟨#Hm, %Hx⟩
  iunfold msgRO at Hm
  icases Hm with ⟨%Hf, #He⟩
  have ho := Msg.index.field (o := m.index) Hx
  obtain ⟨hb, hr⟩ := Msg.index.rel Hf.2.2.2.2.1 ho
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_need g (W32 16) $$ []
  · ipureintro; exact hb
  iapply HΦ
  ipureintro; exact hr

end proof

end AntCheck
end EtcdGrove
end Perennial
