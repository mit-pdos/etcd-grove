/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/ArrLen.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the `[5]int32` fields of an owned message have five elements (what `msgWire` needs)
-/
module

public import Dsverify.Proof.gryff.Wire.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open wire.gryffproto

section generic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [gp_sem : gryff.src.gryffproto.Assumptions]

theorem arr5_len (l : Loc) (dq : DFrac) (a : GoArray w32 5) :
    typedPointsto (GF := GF) l a dq ⊢ typedPointsto l a dq ∗ ⌜a.arr.length = 5⌝ := by
  obtain ⟨xs⟩ := a
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [TypedPointsto.typedPointstoDef]
  iintro ⟨⟨%Hl, Ha⟩, %Hnn⟩
  isplitl
  · iframe; ipureintro; exact ⟨Hl, Hnn⟩
  ipureintro; omega

theorem preAcceptReply_len (t : Loc) (dq : DFrac) (g : PreAcceptReply.Msg) :
    PreAcceptReply.own (GF := GF) t dq g ⊢
      PreAcceptReply.own t dq g ∗ ⌜g.Deps'.arr.length = 5 ∧ g.CommittedDeps'.arr.length = 5⌝ := by
  iintro Ht
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  ihave ⟨CommittedDeps, %h2⟩ := arr5_len _ _ _ $$ CommittedDeps
  isplitl
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro; exact ⟨h1, h2⟩

theorem preAccept_len (t : Loc) (dq : DFrac) (g : PreAccept.Msg) :
    PreAccept.own (GF := GF) t dq g ⊢ PreAccept.own t dq g ∗ ⌜PreAccept.wf g ∧ g.Deps.arr.length = 5⌝ := by
  unfold PreAccept.own
  iintro ⟨%s, Ht, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [PreAccept.goVal]
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  isplitl
  · iexists s
    iframe Hs
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro
    refine ⟨?_, h1⟩
    unfold PreAccept.wf
    have := Hsl.1
    have h63 : sint.Z s.len < 2 ^ 63 := by word
    simp only [sint.nat, sint.Z] at this h63
    omega

theorem accept_len (t : Loc) (dq : DFrac) (g : EAccept.Msg) :
    EAccept.own (GF := GF) t dq g ⊢ EAccept.own t dq g ∗ ⌜EAccept.wf g ∧ g.Deps.arr.length = 5⌝ := by
  unfold EAccept.own
  iintro ⟨%s, Ht, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [EAccept.goVal]
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  isplitl
  · iexists s
    iframe Hs
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro
    refine ⟨?_, h1⟩
    unfold EAccept.wf
    have := Hsl.1
    have h63 : sint.Z s.len < 2 ^ 63 := by word
    simp only [sint.nat, sint.Z] at this h63
    omega

theorem commit_len (t : Loc) (dq : DFrac) (g : ECommit.Msg) :
    ECommit.own (GF := GF) t dq g ⊢ ECommit.own t dq g ∗ ⌜ECommit.wf g ∧ g.Deps.arr.length = 5⌝ := by
  unfold ECommit.own
  iintro ⟨%s, Ht, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [ECommit.goVal]
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  isplitl
  · iexists s
    iframe Hs
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro
    refine ⟨?_, h1⟩
    unfold ECommit.wf
    have := Hsl.1
    have h63 : sint.Z s.len < 2 ^ 63 := by word
    simp only [sint.nat, sint.Z] at this h63
    omega

theorem prepareReply_len (t : Loc) (dq : DFrac) (g : PrepareReply.Msg) :
    PrepareReply.own (GF := GF) t dq g ⊢ PrepareReply.own t dq g ∗ ⌜PrepareReply.wf g ∧ g.Deps.arr.length = 5⌝ := by
  unfold PrepareReply.own
  iintro ⟨%s, Ht, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [PrepareReply.goVal]
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  isplitl
  · iexists s
    iframe Hs
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro
    refine ⟨?_, h1⟩
    unfold PrepareReply.wf
    have := Hsl.1
    have h63 : sint.Z s.len < 2 ^ 63 := by word
    simp only [sint.nat, sint.Z] at this h63
    omega

theorem preAccept_len2 (t : Loc) (dq : DFrac) (g : PreAccept.Msg) (s : GoSlice) :
    (t ↦{dq} PreAccept.goVal g s ∗ s ↦*□ g.Command : IProp GF) ⊢
      (t ↦{dq} PreAccept.goVal g s ∗ s ↦*□ g.Command) ∗ ⌜PreAccept.wf g ∧ g.Deps.arr.length = 5⌝ := by
  iintro ⟨Ht, #Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [PreAccept.goVal]
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  isplitl
  · iframe Hs
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro
    refine ⟨?_, h1⟩
    unfold PreAccept.wf
    have := Hsl.1
    have h63 : sint.Z s.len < 2 ^ 63 := by word
    simp only [sint.nat, sint.Z] at this h63
    omega

theorem accept_len2 (t : Loc) (dq : DFrac) (g : EAccept.Msg) (s : GoSlice) :
    (t ↦{dq} EAccept.goVal g s ∗ s ↦*□ g.Command : IProp GF) ⊢
      (t ↦{dq} EAccept.goVal g s ∗ s ↦*□ g.Command) ∗ ⌜EAccept.wf g ∧ g.Deps.arr.length = 5⌝ := by
  iintro ⟨Ht, #Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [EAccept.goVal]
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  isplitl
  · iframe Hs
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro
    refine ⟨?_, h1⟩
    unfold EAccept.wf
    have := Hsl.1
    have h63 : sint.Z s.len < 2 ^ 63 := by word
    simp only [sint.nat, sint.Z] at this h63
    omega

theorem commit_len2 (t : Loc) (dq : DFrac) (g : ECommit.Msg) (s : GoSlice) :
    (t ↦{dq} ECommit.goVal g s ∗ s ↦*□ g.Command : IProp GF) ⊢
      (t ↦{dq} ECommit.goVal g s ∗ s ↦*□ g.Command) ∗ ⌜ECommit.wf g ∧ g.Deps.arr.length = 5⌝ := by
  iintro ⟨Ht, #Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [ECommit.goVal]
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  isplitl
  · iframe Hs
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro
    refine ⟨?_, h1⟩
    unfold ECommit.wf
    have := Hsl.1
    have h63 : sint.Z s.len < 2 ^ 63 := by word
    simp only [sint.nat, sint.Z] at this h63
    omega

theorem prepareReply_len2 (t : Loc) (dq : DFrac) (g : PrepareReply.Msg) (s : GoSlice) :
    (t ↦{dq} PrepareReply.goVal g s ∗ s ↦*□ g.Command : IProp GF) ⊢
      (t ↦{dq} PrepareReply.goVal g s ∗ s ↦*□ g.Command) ∗ ⌜PrepareReply.wf g ∧ g.Deps.arr.length = 5⌝ := by
  iintro ⟨Ht, #Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [PrepareReply.goVal]
  iStructNamed Ht
  ihave ⟨Deps, %h1⟩ := arr5_len _ _ _ $$ Deps
  isplitl
  · iframe Hs
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · ipureintro
    refine ⟨?_, h1⟩
    unfold PrepareReply.wf
    have := Hsl.1
    have h63 : sint.Z s.len < 2 ^ 63 := by word
    simp only [sint.nat, sint.Z] at this h63
    omega

end generic

end Perennial.gryff.netN
