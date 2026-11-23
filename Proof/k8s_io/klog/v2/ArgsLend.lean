/-
`klog.argsOk` as Perennial's lent `fmt` arguments (klog-printf, 2026-11-23, etcd-grove#25): what
`printfDepth`'s proof passes to `fmt.wp_Fprintf_bytes`. Each `[]string` argument the caller owns
(`klog.strSliceArg`, at its own fraction) is made persistent (`↦*□`: the post's `klog.argsOk` names
the fraction existentially, so the caller gets back a discarded one) and lent to `fmt` under one
fraction (`DFrac.discard`) as `.strings` of a lending function `B` built argument by argument
(`fmt.bytesOwn`, `fmt.argsOkB`). Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.Args
public import Perennial.Proof.fmt.Args

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `klog.argOkAt` with the `[]string`'s elements persistent (`↦*□`). -/
def klog.argOkAtP (d : fmt.Directive) (a : GoInterface) : IProp GF :=
  iprop(fmt.argOkAt fmt.methodVerbs d a ∨
    ∃ (sl : GoSlice) (ss : List GoString),
      ⌜a = interface.mkOk (go.GoType.SliceType go.string) #sl⌝ ∗ sl ↦*□ ss)

instance klog.argOkAtP_persistent (d : fmt.Directive) (a : GoInterface) :
    Persistent (klog.argOkAtP (GF := GF) d a) := by
  unfold klog.argOkAtP; infer_instance

/-- `klog.argsOkAt` with `klog.argOkAtP`. -/
def klog.argsOkAtP : List fmt.Directive → List GoInterface → IProp GF
  | _, [] => iprop(True)
  | d :: ds, a :: xs => iprop(klog.argOkAtP d a ∗ klog.argsOkAtP ds xs)
  | [], a :: xs => iprop(klog.argOkAtP ⟨W8 118, false⟩ a ∗ klog.argsOkAtP [] xs)

instance klog.argsOkAtP_persistent (ds : List fmt.Directive) (xs : List GoInterface) :
    Persistent (klog.argsOkAtP (GF := GF) ds xs) := by
  induction xs generalizing ds with
  | nil => cases ds <;> unfold klog.argsOkAtP <;> infer_instance
  | cons x xs ih => cases ds <;> unfold klog.argsOkAtP <;> infer_instance

/-- Every argument `B` names is lent at `DFrac.discard` (persistent). -/
def klog.lentAll (B : GoInterface → Option fmt.Lent) : IProp GF :=
  iprop(□ ∀ y, fmt.bytesArgOwn DFrac.discard B y)

instance klog.lentAll_persistent (B : GoInterface → Option fmt.Lent) :
    Persistent (klog.lentAll (GF := GF) B) := by
  unfold klog.lentAll; infer_instance

theorem klog.argOkAt_persist (d : fmt.Directive) (a : GoInterface) :
    klog.argOkAt (GF := GF) d a ⊢ |==> klog.argOkAtP d a := by
  unfold klog.argOkAt klog.argOkAtP klog.strSliceArg
  iintro (#H | ⟨%sl, %ss, %dq, %Ha, Hsl⟩)
  · imodintro; ileft; iexact H
  · imod ownSlice_persist $$ Hsl with #Hsl
    imodintro; iright; iexists sl, ss
    isplitr
    · ipureintro; exact Ha
    · iexact Hsl

theorem klog.argOkAtP_weaken (d : fmt.Directive) (a : GoInterface) :
    klog.argOkAtP (GF := GF) d a ⊢ klog.argOkAt d a := by
  unfold klog.argOkAt klog.argOkAtP klog.strSliceArg
  iintro (#H | ⟨%sl, %ss, %Ha, #Hsl⟩)
  · ileft; iexact H
  · iright; iexists sl, ss, DFrac.discard
    isplitr
    · ipureintro; exact Ha
    · iexact Hsl

theorem klog.argsOkAt_persist (ds : List fmt.Directive) (xs : List GoInterface) :
    klog.argsOkAt (GF := GF) ds xs ⊢ |==> klog.argsOkAtP ds xs := by
  induction xs generalizing ds with
  | nil => cases ds <;> (unfold klog.argsOkAt klog.argsOkAtP; iintro -; imodintro; itrivial)
  | cons x xs ih =>
    cases ds with
    | nil =>
      unfold klog.argsOkAt klog.argsOkAtP
      iintro ⟨H, Hs⟩
      imod klog.argOkAt_persist _ _ $$ H with #H
      imod ih [] $$ Hs with #Hs
      imodintro; isplitl []
      · iexact H
      · iexact Hs
    | cons d ds =>
      unfold klog.argsOkAt klog.argsOkAtP
      iintro ⟨H, Hs⟩
      imod klog.argOkAt_persist _ _ $$ H with #H
      imod ih ds $$ Hs with #Hs
      imodintro; isplitl []
      · iexact H
      · iexact Hs

theorem klog.argsOkAtP_weaken (ds : List fmt.Directive) (xs : List GoInterface) :
    klog.argsOkAtP (GF := GF) ds xs ⊢ klog.argsOkAt ds xs := by
  induction xs generalizing ds with
  | nil => cases ds <;> (unfold klog.argsOkAt klog.argsOkAtP; iintro -; itrivial)
  | cons x xs ih =>
    cases ds with
    | nil =>
      unfold klog.argsOkAt klog.argsOkAtP
      iintro ⟨H, Hs⟩
      isplitl [H]
      · iapply klog.argOkAtP_weaken $$ H
      · iapply ih $$ Hs
    | cons d ds =>
      unfold klog.argsOkAt klog.argsOkAtP
      iintro ⟨H, Hs⟩
      isplitl [H]
      · iapply klog.argOkAtP_weaken $$ H
      · iapply ih $$ Hs

/-- `argsOkAtB` holds for a lending function that lends at least what `B` lends. -/
theorem klog.argsOkAtB_mono (B B' : GoInterface → Option fmt.Lent)
    (h : ∀ y, (B y).isSome → (B' y).isSome) (ds : List fmt.Directive) (xs : List GoInterface) :
    fmt.argsOkAtB (GF := GF) B fmt.methodVerbs ds xs ⊢ fmt.argsOkAtB B' fmt.methodVerbs ds xs := by
  have hd : ∀ d x, fmt.argOkAtB (GF := GF) B fmt.methodVerbs d x ⊢
      fmt.argOkAtB B' fmt.methodVerbs d x := by
    intro d x
    unfold fmt.argOkAtB
    iintro (H | %hs)
    · ileft; iexact H
    · iright; ipureintro; exact h x hs
  induction xs generalizing ds with
  | nil => cases ds <;> (unfold fmt.argsOkAtB; iintro -; itrivial)
  | cons x xs ih =>
    cases ds with
    | nil =>
      unfold fmt.argsOkAtB
      iintro ⟨H, Hs⟩
      isplitl [H]
      · iapply hd $$ H
      · iapply ih $$ Hs
    | cons d ds =>
      unfold fmt.argsOkAtB
      iintro ⟨H, Hs⟩
      isplitl [H]
      · iapply hd $$ H
      · iapply ih $$ Hs

/-- One argument added in front: a lending function for it and the rest. -/
theorem klog.lend_cons (d : fmt.Directive) (a : GoInterface) (B' : GoInterface → Option fmt.Lent)
    (ds : List fmt.Directive) (xs : List GoInterface) :
    klog.argOkAtP (GF := GF) d a ∗ klog.lentAll B' ∗ fmt.argsOkAtB B' fmt.methodVerbs ds xs ⊢
      ∃ B, klog.lentAll B ∗ fmt.argOkAtB B fmt.methodVerbs d a ∗
        fmt.argsOkAtB B fmt.methodVerbs ds xs := by
  unfold klog.argOkAtP
  iintro ⟨(#Hf | ⟨%sl, %ss, %Ha, #Hsl⟩), #HB, #Hs⟩
  · iexists B'
    isplitl []
    · iexact HB
    isplitl []
    · unfold fmt.argOkAtB; ileft; iexact Hf
    · iexact Hs
  · by_cases hB : (B' a).isSome
    · iexists B'
      isplitl []
      · iexact HB
      isplitl []
      · unfold fmt.argOkAtB; iright; ipureintro; exact hB
      · iexact Hs
    · classical
      let B : GoInterface → Option fmt.Lent :=
        fun y => if y = a then some (.strings ss) else B' y
      have hBa : B a = some (.strings ss) := by simp [B]
      have hBy : ∀ y, y ≠ a → B y = B' y := by intro y hy; simp [B, hy]
      iexists B
      isplitl []
      · unfold klog.lentAll
        imodintro
        iintro %y
        by_cases hy : y = a
        · subst hy
          unfold fmt.bytesArgOwn
          rw [hBa]
          iexists ⟨go.GoType.SliceType go.string, #sl⟩, sl
          isplitr
          · ipureintro; exact ⟨Ha, rfl, rfl⟩
          · iexact Hsl
        · have he : fmt.bytesArgOwn (GF := GF) DFrac.discard B y =
              fmt.bytesArgOwn DFrac.discard B' y := by
            unfold fmt.bytesArgOwn; rw [hBy y hy]
          rw [he]
          iapply HB
      isplitl []
      · unfold fmt.argOkAtB; iright; ipureintro; rw [hBa]; rfl
      · iapply klog.argsOkAtB_mono B' B ?_ $$ Hs
        intro y hs
        by_cases hy : y = a
        · subst hy; rw [hBa]; rfl
        · rw [hBy y hy]; exact hs

/-- The persistent arguments, lent: a lending function `B` naming every `[]string`. -/
theorem klog.argsOkAtP_lend (ds : List fmt.Directive) (xs : List GoInterface) :
    klog.argsOkAtP (GF := GF) ds xs ⊢
      ∃ B, klog.lentAll B ∗ fmt.argsOkAtB B fmt.methodVerbs ds xs := by
  induction xs generalizing ds with
  | nil =>
    iintro -
    iexists (fun _ => none)
    isplitl []
    · unfold klog.lentAll; imodintro; iintro %y; unfold fmt.bytesArgOwn; itrivial
    · cases ds <;> (unfold fmt.argsOkAtB; itrivial)
  | cons x xs ih =>
    cases ds with
    | nil =>
      unfold klog.argsOkAtP fmt.argsOkAtB
      iintro ⟨#H, #Hs⟩
      icases ih [] $$ Hs with ⟨%B', #HB, #Hs'⟩
      iapply klog.lend_cons $$ [H HB Hs']
      iframe #
    | cons d ds =>
      unfold klog.argsOkAtP fmt.argsOkAtB
      iintro ⟨#H, #Hs⟩
      icases ih ds $$ Hs with ⟨%B', #HB, #Hs'⟩
      iapply klog.lend_cons $$ [H HB Hs']
      iframe #

theorem klog.lentAll_bytesOwn (B : GoInterface → Option fmt.Lent) (xs : List GoInterface) :
    klog.lentAll (GF := GF) B ⊢ fmt.bytesOwn DFrac.discard B xs := by
  unfold fmt.bytesOwn
  induction xs with
  | nil => iintro -; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons x xs ih =>
    iintro #HB
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iunfold klog.lentAll at HB
      iapply HB
    · iapply ih $$ HB

/-- **`klog.argsOk`, lent to `fmt`**: a lending function `B` whose contents are lent at
`DFrac.discard`, the arguments `fmt.argsOkB B` the format, and `klog.argsOk` itself back (its
`[]string`s at the discarded fraction). -/
theorem klog.argsOk_lend (f : GoString) (xs : List GoInterface) :
    klog.argsOk (GF := GF) f xs ⊢ |==> ∃ B, fmt.bytesOwn DFrac.discard B xs ∗
      fmt.argsOkB B fmt.methodVerbs f xs ∗ klog.argsOk f xs := by
  unfold klog.argsOk
  iintro ⟨%ds, %hds, H⟩
  imod klog.argsOkAt_persist _ _ $$ H with #H
  icases klog.argsOkAtP_lend _ _ $$ H with ⟨%B, #HB, #HokB⟩
  imodintro
  iexists B
  isplitl []
  · iapply klog.lentAll_bytesOwn $$ HB
  isplitl []
  · unfold fmt.argsOkB; iright; iexists ds
    isplitl []
    · ipureintro; exact hds
    · iexact HokB
  · iexists ds
    isplitl []
    · ipureintro; exact hds
    · iapply klog.argsOkAtP_weaken $$ H

end defs

end EtcdGrove
end Perennial
