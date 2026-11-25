/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Access.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: reading an instance's fields through the lock's contents
-/
module

public import Dsverify.Proof.gryff.X.Helpers
public import Dsverify.Proof.gryff.X.Tag
public import Dsverify.Proof.gryff.X.Sort

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy Msg Ev Out)
open Perennial.gryff.replica (XS Node)
open Perennial.gryff.replica2 (Repl2Names)
open Perennial.gryff.pure (stOf)
open github_com.goose_lang.primitive (ProphId)

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [gryff_sem : src.gryff.Assumptions]
variable {k : Fin 3} {ρ : Repl2Names} {r h : Loc} {p : ProphId}

set_option goose.wp.extras true

/-- Reading `w.Cmds` (the executor's waits). -/
theorem wp_LA_load_Cmds (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) (n : Node)
    (pw : Loc) :
    {{ L.LA t xs ∗ ghostMapElem ρ.ptrs n DFrac.discard pw }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType src.state.Command.ty))))
        (Val #(pw.[src.gryff.Instance, go!"Cmds"])))
    {{ (cs : GoSlice), RET #cs; L.LA t xs }} := by
  iintro %Φ ⟨HLA, #Hn⟩ HΦ
  icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
    %cu, %pm, #HhR, #HnoC, #HIS, #Hisp, #Hcrt, #Hc1, #Hc1s, #Hms, #Hpvt, Hcu, Hcrtv, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
  ihave %HnM := ghost_map_lookup $$ HM Hn
  icases instsG_upd ρ xs (stOf k t) M n pw HnM $$ Hinsts with ⟨⟨%c, %Hc, Hi⟩, Hclose⟩
  icases (copyRepG_open ..).1 $$ Hi with ⟨%iv, Hp, Hcm, Hlb, %Hiv⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_apply IntoValTyped.wp_load (t := go.GoType.SliceType src.state.Command.ty) _ _ _ $$ Cmds
    as Cmds
  ihave Hp : pw ↦ iv $$ [-HΦ HTH HPr HRs Hxs1 HPO HBt Hcu Hcrtv HM HMe Hrows Hclose Hmono Hconfs Hconf
    Hpm Hrst Hcm Hlb]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  ihave Hinsts := Hclose $$ %xs %(stOf k t) [] [] [Hp Hcm Hlb]
  · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
  · ipureintro; intro _ _ _; rfl
  · iexists c; isplitr; · ipureintro; exact Hc
    iapply (copyRepG_open ..).2; iexists iv; iframe; ipureintro; exact Hiv
  iapply HΦ
  iapply (L.LA_open ..).2; iframe
  iapply (epaxosOwnG_open ..).2
  iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
  iframe; iframe #; ipureintro; exact Hep

/-- Reading a command's `K` (a persistent command). -/
theorem wp_load_cmd_K (l : Loc) (g : src.state.Command) :
    {{ (l ↦□ g : IProp GF) }}
      (App (Val (GoInstruction (GoLoad src.state.Key.ty))) (Val #(l.[src.state.Command, go!"K"])))
    {{ RET #g.K'; True }} := by
  iintro %Φ #Hl HΦ
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨#Hl, %Hnn⟩
  iStructNamed Hl
  wp_apply IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _ $$ K as -
  iapply HΦ; itrivial

/-- Reading a command's `OldValue` (a persistent command). -/
theorem wp_load_cmd_OldValue (l : Loc) (g : src.state.Command) :
    {{ (l ↦□ g : IProp GF) }}
      (App (Val (GoInstruction (GoLoad src.state.Value.ty))) (Val #(l.[src.state.Command, go!"OldValue"])))
    {{ RET #g.OldValue'; True }} := by
  iintro %Φ #Hl HΦ
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨#Hl, %Hnn⟩
  iStructNamed Hl
  wp_apply IntoValTyped.wp_load (t := src.state.Value.ty) _ _ _ $$ OldValue as -
  iapply HΦ; itrivial

/-- Reading a command's `V` (a persistent command). -/
theorem wp_load_cmd_V (l : Loc) (g : src.state.Command) :
    {{ (l ↦□ g : IProp GF) }}
      (App (Val (GoInstruction (GoLoad src.state.Value.ty))) (Val #(l.[src.state.Command, go!"V"])))
    {{ RET #g.V'; True }} := by
  iintro %Φ #Hl HΦ
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨#Hl, %Hnn⟩
  iStructNamed Hl
  wp_apply IntoValTyped.wp_load (t := src.state.Value.ty) _ _ _ $$ V as -
  iapply HΦ; itrivial

/-- `w.Base.T.GreaterThan(t)` on an instance's struct. -/
theorem wp_inst_Base_GreaterThan (pw : Loc) (iw : src.gryff.Instance) (tb : src.gryffproto.Tag) :
    {{ (pw ↦ iw : IProp GF) }}
      (App (Val ((pw.[src.gryff.Instance, go!"Base"]).[src.gryffproto.ValTag, go!"T"] @!!
        go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"GreaterThan")) (Val #tb))
    {{ RET #((replica2.tagOf iw.Base'.T').gt (replica2.tagOf tb)); pw ↦ iw }} := by
  iintro %Φ Hp HΦ
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  icases typedPointsto_not_null_dup _ _ _ $$ Base with ⟨Base, %Hnn2⟩
  iStructNamed Base
  wp_apply wp_Tag_GreaterThan _ iw.Base'.T' tb $$ [$T] as T
  iapply HΦ
  ihave Base : pw.[src.gryff.Instance, go!"Base"] ↦ iw.Base' $$ [V T]
  · iapply typedPointsto_combine _ _ _ Hnn2
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iFrameNamed

theorem inst_deps_len (p : Loc) (iv : src.gryff.Instance) :
    (p ↦ iv : IProp GF) ⊢ p ↦ iv ∗ ⌜iv.Deps'.arr.length = 5⌝ := by
  iintro Hp
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  ihave %Hl := array_len (V := w32) _ _ 5 iv.Deps'.arr $$ Deps
  isplitl
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  ipureintro; omega

/-- Reading an instance's `Status` in the instance space at state `s`. -/
theorem wp_insts_load_Status (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (hp : M.lookup n = some p) :
    {{ instsG (GF := GF) ρ xs s M }}
      (App (Val (GoInstruction (GoLoad go.int8))) (Val #(p.[src.gryff.Instance, go!"Status"])))
    {{ (x : w8), RET #x; instsG ρ xs s M ∗ ⌜∃ c iv, s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c ∧
        copyFacts xs n iv c ∧ x = iv.Status'⌝ }} := by
  iintro %Φ H HΦ
  icases (instsG_acc ρ xs s M n p hp).1 $$ H with ⟨⟨%c, %hc, Hc⟩, Hrest⟩
  icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, Hp, Hcm, Hlb, %Hf⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_apply IntoValTyped.wp_load (t := go.int8) _ _ _ $$ Status as Status
  ihave Hp : p ↦ iv $$ [-HΦ Hrest Hcm Hlb]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  iapply HΦ
  isplitl
  · iapply (instsG_acc ρ xs s M n p hp).2
    iframe Hrest
    iexists c
    isplitr; · ipureintro; exact hc
    iapply (copyRepG_open ..).2
    iexists iv; iframe; ipureintro; exact Hf
  ipureintro; exact ⟨c, iv, hc, Hf, rfl⟩

/-- Reading an instance's `Index` in the instance space at state `s`. -/
theorem wp_insts_load_Index (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (hp : M.lookup n = some p) :
    {{ instsG (GF := GF) ρ xs s M }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(p.[src.gryff.Instance, go!"Index"])))
    {{ (x : w64), RET #x; instsG ρ xs s M ∗ ⌜∃ c iv, s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c ∧
        copyFacts xs n iv c ∧ x = iv.Index'⌝ }} := by
  iintro %Φ H HΦ
  icases (instsG_acc ρ xs s M n p hp).1 $$ H with ⟨⟨%c, %hc, Hc⟩, Hrest⟩
  icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, Hp, Hcm, Hlb, %Hf⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_apply IntoValTyped.wp_load (t := go.int) _ _ _ $$ Index as Index
  ihave Hp : p ↦ iv $$ [-HΦ Hrest Hcm Hlb]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  iapply HΦ
  isplitl
  · iapply (instsG_acc ρ xs s M n p hp).2
    iframe Hrest
    iexists c
    isplitr; · ipureintro; exact hc
    iapply (copyRepG_open ..).2
    iexists iv; iframe; ipureintro; exact Hf
  ipureintro; exact ⟨c, iv, hc, Hf, rfl⟩

/-- Reading an instance's `Lowlink` in the instance space at state `s`. -/
theorem wp_insts_load_Lowlink (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (hp : M.lookup n = some p) :
    {{ instsG (GF := GF) ρ xs s M }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(p.[src.gryff.Instance, go!"Lowlink"])))
    {{ (x : w64), RET #x; instsG ρ xs s M ∗ ⌜∃ c iv, s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c ∧
        copyFacts xs n iv c ∧ x = iv.Lowlink'⌝ }} := by
  iintro %Φ H HΦ
  icases (instsG_acc ρ xs s M n p hp).1 $$ H with ⟨⟨%c, %hc, Hc⟩, Hrest⟩
  icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, Hp, Hcm, Hlb, %Hf⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_apply IntoValTyped.wp_load (t := go.int) _ _ _ $$ Lowlink as Lowlink
  ihave Hp : p ↦ iv $$ [-HΦ Hrest Hcm Hlb]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  iapply HΦ
  isplitl
  · iapply (instsG_acc ρ xs s M n p hp).2
    iframe Hrest
    iexists c
    isplitr; · ipureintro; exact hc
    iapply (copyRepG_open ..).2
    iexists iv; iframe; ipureintro; exact Hf
  ipureintro; exact ⟨c, iv, hc, Hf, rfl⟩

/-- Reading an instance's `Cmds` in the instance space at state `s`. -/
theorem wp_insts_load_Cmds (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (hp : M.lookup n = some p) :
    {{ instsG (GF := GF) ρ xs s M }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType src.state.Command.ty)))) (Val #(p.[src.gryff.Instance, go!"Cmds"])))
    {{ (x : GoSlice), RET #x; instsG ρ xs s M ∗ ⌜∃ c iv, s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c ∧
        copyFacts xs n iv c ∧ x = iv.Cmds'⌝ }} := by
  iintro %Φ H HΦ
  icases (instsG_acc ρ xs s M n p hp).1 $$ H with ⟨⟨%c, %hc, Hc⟩, Hrest⟩
  icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, Hp, Hcm, Hlb, %Hf⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_apply IntoValTyped.wp_load (t := (go.GoType.SliceType src.state.Command.ty)) _ _ _ $$ Cmds as Cmds
  ihave Hp : p ↦ iv $$ [-HΦ Hrest Hcm Hlb]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  iapply HΦ
  isplitl
  · iapply (instsG_acc ρ xs s M n p hp).2
    iframe Hrest
    iexists c
    isplitr; · ipureintro; exact hc
    iapply (copyRepG_open ..).2
    iexists iv; iframe; ipureintro; exact Hf
  ipureintro; exact ⟨c, iv, hc, Hf, rfl⟩

end

end Perennial.gryff.X
