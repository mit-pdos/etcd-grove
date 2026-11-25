module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section log
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogSpecs GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem argOk_wf (ii : GoInterfaceOk) (h : fmt.ArgWf ii) : ⊢ argOk (GF := GF) (interface.ok ii) := by
  unfold argOk
  ileft; ipureintro
  intro ii' h'
  cases h'
  exact Or.inl h

theorem argOk_string (x : GoString) : ⊢ argOk (GF := GF) (interface.mkOk go.string #x) := by
  unfold argOk
  ileft; ipureintro
  intro ii' h'
  have := fmt.ArgsWf.cons_string x [] fmt.ArgsWf.nil
  exact Or.inl (this ii' (by rw [h']; simp))

theorem argOk_u64 (x : w64) : ⊢ argOk (GF := GF) (interface.mkOk go.uint64 #x) := by
  unfold argOk
  ileft; ipureintro
  intro ii' h'
  have := fmt.ArgsWf.cons_int _ _ [] (.uint64 x) fmt.ArgsWf.nil
  exact Or.inl (this ii' (by rw [← h']; simp [interface.mkOk]))

theorem argOk_noMethods (t : go.GoType) (v : val) (hE : go.typeSetContains t go.error = false)
    (hS : go.typeSetContains t fmt.Stringer.ty = false) :
    ⊢ argOk (GF := GF) (interface.mkOk t v) := by
  unfold argOk
  ileft; ipureintro
  intro ii' h'
  cases h'
  exact Or.inr ⟨hE, hS⟩

theorem argOk_err (e : GoInterface) : models_lab.errAny (GF := GF) e ⊢ argOk e := by
  iintro #H
  unfold argOk
  iright; iexact H

theorem argOks0 : ⊢ [∗list] x ∈ ([] : List GoInterface), argOk (GF := GF) x :=
  BI.BigSepL.bigSepL_nil_intro (P := iprop(emp))

theorem argOks_cons (a : GoInterface) (l : List GoInterface) :
    argOk (GF := GF) a ∗ ([∗list] x ∈ l, argOk (GF := GF) x) ⊢
      [∗list] x ∈ a :: l, argOk (GF := GF) x :=
  BI.BigSepL.bigSepL_cons (Φ := fun _ x => argOk (GF := GF) x).2

theorem argOks1 (a : GoInterface) : argOk (GF := GF) a ⊢ [∗list] x ∈ [a], argOk (GF := GF) x := by
  iintro #Ha
  iapply argOks_cons
  iframe Ha
  iapply argOks0

theorem argOks2 (a b : GoInterface) :
    argOk (GF := GF) a ∗ argOk (GF := GF) b ⊢ [∗list] x ∈ [a, b], argOk (GF := GF) x := by
  iintro ⟨#Ha, #Hb⟩
  iapply argOks_cons
  iframe Ha
  iapply argOks1 $$ Hb

theorem argOks3 (a b c : GoInterface) :
    argOk (GF := GF) a ∗ argOk (GF := GF) b ∗ argOk (GF := GF) c ⊢
      [∗list] x ∈ [a, b, c], argOk (GF := GF) x := by
  iintro ⟨#Ha, #Hb, #Hc⟩
  iapply argOks_cons
  iframe Ha
  iapply argOks2 $$ [Hb Hc]
  iframe Hb Hc

/-- `l.Printf(format, args...)` on arguments `argOk` allows. -/
theorem wp_Logger_Printf (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface)
    (dq : DFrac) (hl : l ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk (GF := GF) x }}
      (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
        (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  exact LogSpecs.wp_Logger_Printf l msg arg xs dq hl

/-- `l.Println(args...)` on arguments `argOk` allows. -/
theorem wp_Logger_Println (l : Loc) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (hl : l ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk (GF := GF) x }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  exact LogSpecs.wp_Logger_Println l arg xs dq hl

/-- `wp_Logger_Printf` with the argument slice first (for `wp_log`). -/
theorem wp_Logger_Printf' (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface) :
    ⊢ ∀ Φ : val → IProp GF, ⌜l ≠ null⌝ -∗ arg ↦* xs -∗ isPkgInit (PROP := IProp GF) pkg_id.log -∗
      ([∗list] x ∈ xs, argOk (GF := GF) x) -∗ Φ #() -∗
      WP (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
        (Val #arg)) {{ Φ }} := by
  iintro %Φ %hl Hs #Hpkg #Hok HΦ
  wp_apply wp_Logger_Printf l msg arg xs (DFrac.own 1) hl $$ [$Hs $Hok] as -
  iexact HΦ

theorem wp_Logger_Println' (l : Loc) (arg : GoSlice) (xs : List GoInterface) :
    ⊢ ∀ Φ : val → IProp GF, ⌜l ≠ null⌝ -∗ arg ↦* xs -∗ isPkgInit (PROP := IProp GF) pkg_id.log -∗
      ([∗list] x ∈ xs, argOk (GF := GF) x) -∗ Φ #() -∗
      WP (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
        {{ Φ }} := by
  iintro %Φ %hl Hs #Hpkg #Hok HΦ
  wp_apply wp_Logger_Println l arg xs (DFrac.own 1) hl $$ [$Hs $Hok] as -
  iexact HΦ

end log

set_option hygiene false in
/-- A `n.log.Printf(fmt, args...)` call at the head of the program, with the arguments `l`: the
argument slice, then the call (the logger non-nil: a hypothesis `_ ≠ null` or `Hch`, `nodeFields`'
pure part); leaves the goal `[∗list] x ∈ l, argOk x`, then the
continuation. -/
macro "wp_log " l:term : tactic => `(tactic| (
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any) $l
  wp_auto
  isplitl []
  focus (ipureintro; rfl)
  iintro %args_sl ⟨Hargs, -⟩
  wp_auto
  wp_apply wp_Logger_Printf' $$ [] Hargs
  focus (ipureintro; first | assumption | exact Hch.2)))

set_option hygiene false in
/-- The same for `n.log.Println(args...)`. -/
macro "wp_logln " l:term : tactic => `(tactic| (
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any) $l
  wp_auto
  isplitl []
  focus (ipureintro; rfl)
  iintro %args_sl ⟨Hargs, -⟩
  wp_auto
  wp_apply wp_Logger_Println' $$ [] Hargs
  focus (ipureintro; first | assumption | exact Hch.2)))

end NodeP

end github_com.despreston.go_craq

end Perennial
