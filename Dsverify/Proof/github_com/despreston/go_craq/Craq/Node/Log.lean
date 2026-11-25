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
variable [sem : go.Semantics] [log.Assumptions] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions] [LogSpecs GF]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem argOk_wf (ii : GoInterfaceOk) (h : fmt.ArgWf ii) : ⊢ argOk (GF := GF) (interface.ok ii) := by
  unfold argOk
  iright; ileft; ipureintro
  exact ⟨ii, rfl, h⟩

theorem argOk_string (x : GoString) : ⊢ argOk (GF := GF) (interface.mkOk go.string #x) := by
  unfold argOk
  iright; ileft; ipureintro
  exact ⟨_, rfl, fmt.ArgsWf.cons_string x [] fmt.ArgsWf.nil _ List.mem_cons_self⟩

theorem argOk_u64 (x : w64) : ⊢ argOk (GF := GF) (interface.mkOk go.uint64 #x) := by
  unfold argOk
  iright; ileft; ipureintro
  exact ⟨_, rfl, fmt.ArgsWf.cons_int _ _ [] (.uint64 x) fmt.ArgsWf.nil _ List.mem_cons_self⟩

/-- A store item, its `Key`, `Version`, `Value` and bytes persistent (`itemPtr`). -/
theorem argOk_item (p : Loc) (k : GoString) (v : w64) (x : GoString) :
    itemPtr (hG := hG) p k v x ⊢
      argOk (GF := GF) (interface.mkOk (go.GoType.PointerType store.Item.ty) #p) := by
  unfold itemPtr argOk
  iintro ⟨#Hk, #Hv, %sl, #Hsl, #Hx⟩
  iright; iright; ileft
  iexists p, k, v, sl, x
  iframe Hk Hv Hsl Hx
  ipureintro; rfl

/-- A `*transport.NodeMeta` with a fraction of its points-to. -/
theorem argOk_meta (p : Loc) (dq : DFrac) (m : transport.NodeMeta) :
    p ↦{dq} m ⊢ argOk (GF := GF) (interface.mkOk (go.GoType.PointerType transport.NodeMeta.ty) #p) := by
  iintro Hp
  unfold argOk
  iright; iright; iright; ileft
  iexists p, dq, m
  iframe Hp
  ipureintro; rfl

theorem argOk_errPlain (e : GoInterface) : models_lab.errPlain (GF := GF) e ⊢ argOk e := by
  iintro #H
  unfold argOk
  iright; iright; iright; iright; iexact H

theorem argOks0 : ⊢ [∗list] x ∈ ([] : List GoInterface), argOk (GF := GF) x :=
  BI.BigSepL.bigSepL_nil_intro (P := iprop(emp))

theorem argOks_cons (a : GoInterface) (l : List GoInterface) :
    argOk (GF := GF) a ∗ ([∗list] x ∈ l, argOk (GF := GF) x) ⊢
      [∗list] x ∈ a :: l, argOk (GF := GF) x :=
  BI.BigSepL.bigSepL_cons (Φ := fun _ x => argOk (GF := GF) x).2

theorem argOks1 (a : GoInterface) : argOk (GF := GF) a ⊢ [∗list] x ∈ [a], argOk (GF := GF) x := by
  iintro Ha
  iapply argOks_cons
  isplitl [Ha]
  · iexact Ha
  iapply argOks0

theorem argOks2 (a b : GoInterface) :
    argOk (GF := GF) a ∗ argOk (GF := GF) b ⊢ [∗list] x ∈ [a, b], argOk (GF := GF) x := by
  iintro ⟨Ha, Hb⟩
  iapply argOks_cons
  isplitl [Ha]
  · iexact Ha
  iapply argOks1 $$ Hb

theorem argOks3 (a b c : GoInterface) :
    argOk (GF := GF) a ∗ argOk (GF := GF) b ∗ argOk (GF := GF) c ⊢
      [∗list] x ∈ [a, b, c], argOk (GF := GF) x := by
  iintro ⟨Ha, Hb, Hc⟩
  iapply argOks_cons
  isplitl [Ha]
  · iexact Ha
  iapply argOks2 $$ [Hb Hc]
  iframe Hb Hc

/-- `l.Printf(format, args...)` on arguments `argOk` allows. -/
theorem wp_Logger_Printf (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface)
    (dq : DFrac) (hl : StdLogger l) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk (GF := GF) x }}
      (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
        (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  iintro %Φ ⟨#Hpkg, Hs, Hok⟩ HΦ
  wp_apply LogSpecs.wp_Logger_Printf l msg arg xs dq hl $$ [$Hpkg $Hs $Hok] as ⟨Hs, -⟩
  iapply HΦ $$ Hs

/-- `l.Println(args...)` on arguments `argOk` allows. -/
theorem wp_Logger_Println (l : Loc) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (hl : StdLogger l) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk (GF := GF) x }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  iintro %Φ ⟨#Hpkg, Hs, Hok⟩ HΦ
  wp_apply LogSpecs.wp_Logger_Println l arg xs dq hl $$ [$Hpkg $Hs $Hok] as ⟨Hs, -⟩
  iapply HΦ $$ Hs

/-- `wp_Logger_Printf` with the argument slice first (for `wp_log`). -/
theorem wp_Logger_Printf' (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface) :
    ⊢ ∀ Φ : val → IProp GF, ⌜StdLogger l⌝ -∗ arg ↦* xs -∗ isPkgInit (PROP := IProp GF) pkg_id.log -∗
      ([∗list] x ∈ xs, argOk (GF := GF) x) -∗ Φ #() -∗
      WP (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
        (Val #arg)) {{ Φ }} := by
  iintro %Φ %hl Hs #Hpkg Hok HΦ
  wp_apply wp_Logger_Printf l msg arg xs (DFrac.own 1) hl $$ [$Hs $Hok] as -
  iexact HΦ

/-- `wp_Logger_Printf'` with the arguments' condition before the package (for `wp_log_ok`). -/
theorem wp_Logger_Printf_ok (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface) :
    ⊢ ∀ Φ : val → IProp GF, ⌜StdLogger l⌝ -∗ arg ↦* xs -∗ ([∗list] x ∈ xs, argOk (GF := GF) x) -∗
      isPkgInit (PROP := IProp GF) pkg_id.log -∗ Φ #() -∗
      WP (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
        (Val #arg)) {{ Φ }} := by
  iintro %Φ %hl Hs Hok #Hpkg HΦ
  iapply wp_Logger_Printf' $$ %Φ %hl Hs Hpkg Hok HΦ

theorem wp_Logger_Println' (l : Loc) (arg : GoSlice) (xs : List GoInterface) :
    ⊢ ∀ Φ : val → IProp GF, ⌜StdLogger l⌝ -∗ arg ↦* xs -∗ isPkgInit (PROP := IProp GF) pkg_id.log -∗
      ([∗list] x ∈ xs, argOk (GF := GF) x) -∗ Φ #() -∗
      WP (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
        {{ Φ }} := by
  iintro %Φ %hl Hs #Hpkg Hok HΦ
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
/-- `wp_log` whose arguments' condition is the spatial hypothesis `Hok` (made before the call:
an argument whose condition is not persistent). -/
macro "wp_log_ok " l:term : tactic => `(tactic| (
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any) $l
  wp_auto
  isplitl []
  focus (ipureintro; rfl)
  iintro %args_sl ⟨Hargs, -⟩
  wp_auto
  wp_apply wp_Logger_Printf_ok $$ [] Hargs Hok
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
