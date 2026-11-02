/- Lean-first (no Rocq counterpart).

# The closures of linearizability (2026-11-02)

The closures of `Closures.lean` as lemmas (they are values, not functions of the package, so they
have no spec file): `RealTime` (`wp_rtV`) and `GeneralLikely` (`wp_glV`), whose answers are
`rtOrder` and `glOrder`, and `RVal`'s `Init` and `Step` (`wp_rvInitV`, `wp_rvStepV`), which call
the model's `Init` and `StepContext`.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Defs
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Closures

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.anishathalye.porcupine

section orders
variable [GooseExts]

/-- `RealTime`'s answer: `HardBefore` if `a` returns before `b` is called, `HardAfter` if `a` is
called after `b` returns, else `DontKnow`. -/
def rtOrder (a b : Operation) : w64 :=
  if sint.Z a.Return' < sint.Z b.Call' then W64 (-2)
  else if sint.Z b.Return' < sint.Z a.Call' then W64 2
  else W64 0

/-- `GeneralLikely`'s answer: `SoftBefore`, `SoftAfter` or `DontKnow` as `a`'s call is before,
after or at `b`'s. -/
def glOrder (a b : Operation) : w64 :=
  if sint.Z a.Call' < sint.Z b.Call' then W64 (-1)
  else if sint.Z b.Call' < sint.Z a.Call' then W64 1
  else W64 0

end orders

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option hygiene false in
/-- Split `Ha : pa ↦{qa} a`, `Hb : pb ↦{qb} b` (two `Operation`s) into their fields, keeping
`pa ≠ null`, `pb ≠ null` (`Hna`, `Hnb`) to put them back (`op_join`). -/
local macro "op_split" : tactic => `(tactic| (
  icases typedPointsto_not_null_dup pa a qa $$ Ha with ⟨Ha, %Hna⟩
  icases typedPointsto_not_null_dup pb b qb $$ Hb with ⟨Hb, %Hnb⟩
  iStructNamedSuffix Ha "a"
  irename : (pa.[Operation, go!"_#8"] ↦{qa} a.«_#8'» : IProp GF) => Za
  iStructNamedSuffix Hb "b"
  irename : (pb.[Operation, go!"_#8"] ↦{qb} b.«_#8'» : IProp GF) => Zb))

set_option hygiene false in
/-- Prove `pa ↦{qa} a ∗ pb ↦{qb} b` from the fields `op_split` made. -/
local macro "op_join" : tactic => `(tactic| (
  isplitl [ClientIda OpKinda Inputa Calla Outputa Returna Metadataa OrderHinta Za]
  · iapply typedPointsto_combine pa a qa Hna
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · iapply typedPointsto_combine pb b qb Hnb
    simp only [TypedPointsto.typedPointstoDef]
    iframe))

theorem wp_rtV (pa pb : Loc) (a b : Operation) (qa qb : DFrac) :
    {{ (pa ↦{qa} a : IProp GF) ∗ pb ↦{qb} b }}
      (App (App (Val #rtV) (Val #pa)) (Val #pb))
    {{ RET (PairV #(rtOrder a b) #interface.nil); pa ↦{qa} a ∗ pb ↦{qb} b }} := by
  wp_start as ⟨Ha, Hb⟩
  op_split
  rw [rtV_val]
  wp_auto
  wp_if_destruct
  · simp only [HardBefore]
    wp_auto
    rw [show rtOrder a b = W64 (-2) by unfold rtOrder; simp [Hif]]
    iapply HΦ
    op_join
  · wp_if_destruct
    · simp only [HardAfter]
      wp_auto
      rw [show rtOrder a b = W64 2 by rename_i h1; unfold rtOrder; simp [h1, Hif]]
      iapply HΦ
      op_join
    · simp only [DontKnow]
      wp_auto
      rw [show rtOrder a b = W64 0 by rename_i h1; unfold rtOrder; simp [h1, Hif]]
      iapply HΦ
      op_join

theorem wp_glV (pa pb : Loc) (a b : Operation) (qa qb : DFrac) :
    {{ (pa ↦{qa} a : IProp GF) ∗ pb ↦{qb} b }}
      (App (App (Val #glV) (Val #pa)) (Val #pb))
    {{ RET (PairV #(glOrder a b) #interface.nil); pa ↦{qa} a ∗ pb ↦{qb} b }} := by
  wp_start as ⟨Ha, Hb⟩
  op_split
  rw [glV_val]
  wp_auto
  wp_if_destruct
  · simp only [SoftBefore]
    wp_auto
    rw [show glOrder a b = W64 (-1) by unfold glOrder; simp [Hif]]
    iapply HΦ
    op_join
  · wp_if_destruct
    · simp only [SoftAfter]
      wp_auto
      rw [show glOrder a b = W64 1 by rename_i h1; unfold glOrder; simp [h1, Hif]]
      iapply HΦ
      op_join
    · simp only [DontKnow]
      wp_auto
      rw [show glOrder a b = W64 0 by rename_i h1; unfold glOrder; simp [h1, Hif]]
      iapply HΦ
      op_join

/-- `RVal.Init(model)` is `model.Init()`. -/
theorem wp_rvInitV {σ : Type} (S : ModelSpec GF σ) (m : Model) :
    {{ initSpec S m.Init' }}
      (App (Val #rvInitV) (Val #m))
    {{ (v : GoInterface), RET #v; S.rep 0 v S.M.init }} := by
  wp_start as #Hinit
  rw [rvInitV_val]
  wp_auto
  unfold initSpec
  wp_apply Hinit as %v Hv
  iapply HΦ $$ Hv

end proofs

section proofs_hasLC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- `RVal.Step(ctx, state, input, output, model)` is `model.StepContext(ctx, state, input,
output)`. -/
theorem wp_rvStepV {σ : Type} (S : ModelSpec GF σ) (m : Model) (c : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (k : Nat) (v : GoInterface) (s : σ)
    (i o : GoInterface) :
    {{ stepCtxSpec S m.StepContext' ∗ context.isContext c cs ∗ ⌜k < 2 ^ 60⌝ ∗ S.rep k v s ∗
        S.ioOk i o }}
      (App (App (App (App (App (Val #rvStepV) (Val #(GoInterface.ok c))) (Val #v)) (Val #i))
        (Val #o)) (Val #m))
    {{ (ok : Bool) (v' : GoInterface), RET (PairV #ok #v');
        S.rep k v s ∗
        ((⌜ok = (S.M.step s (i, o)).isSome⌝ ∗ stepPost S k s (i, o) v') ∨
          (⌜ok = false⌝ ∗ □ cs.PDone)) }} := by
  wp_start as ⟨#Hstep, Hctx, %Hk, Hrep, #Hio⟩
  rw [rvStepV_val]
  wp_auto
  unfold stepCtxSpec
  wp_apply Hstep $$ %c %cs %k %v %s %i %o [$Hctx $Hrep $Hio] as %ok %v' Hpost
  · ipureintro; exact Hk
  iapply HΦ $$ Hpost

end proofs_hasLC

end github_com.anishathalye.porcupine

end Perennial
