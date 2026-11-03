/- Lean-first (no Rocq counterpart).

The proof of `GetAny`'s logically atomic spec. The patched code (`etc/proph-patches/prophkv/`)
creates a prophecy `p` first, and resolves it with the random choice `r % 2 == 0` (true: the first
read's answer is returned) once it is drawn. At the first read, the proof reads the prophecy: if
it says the first answer is returned (`firstWins`), the caller's update fires there, with that
answer; otherwise it is kept, and fires at the second read. The resolution then tells which branch
the code takes, and the other combination is impossible.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.prophkv.GetAny
public import Spec.github_com.mit_pdos.etcd_grove.examples.prophkv.KV__Get

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.prophkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

/-- The prophecy says that `GetAny` returns the first read's answer. -/
def firstWins (pvs : List val) : Prop := pvs.head? = some (#true : val)

/-- The first read's outcome: the caller's update fired with its answer (the prophecy says it is
returned), or not, the update kept. -/
def firstRead (γ : GName) (k : GoString) (pvs : List val) (Q : GoString → IProp GF)
    (v1 : GoString) : IProp GF :=
  iprop((⌜firstWins pvs⌝ ∗ Q v1) ∨
    (⌜¬ firstWins pvs⌝ ∗ AU <{ ∃∃ (m : GMap GoString GoString), kvState γ m }> @ ⊤, ∅
      <{ kvState γ m, COMM Q ((m !! k).getD go!"") }>))

/-- `go.prophId` is no interface: Perennial's `NotInterface` instances do not unfold the
predeclared types, so it is stated here, as in `examples/linkvtxn`'s `Proph.lean` (a Perennial
gap, `notes/perennial-changes.md`). The value method's `MethodResolve ProphId.ty` needs it. -/
instance notInterface_prophId : go.NotInterface go.prophId := ⟨by unfold go.prophId; trivial⟩

/-- `l.ResolveBool(b)` on a `*ProphId` `l` holding `p` (as goose calls the value method on the
patch's variable): the next of the prophesied values is `#b`. -/
theorem wp_ptr_ResolveBool (l : Loc) (dq : DFrac) (p : github_com.goose_lang.primitive.ProphId)
    (pvs : List val) (b : Bool) :
    {{ typedPointsto (GF := GF) l p dq ∗ proph p pvs }}
      (App (Val (l @!! go.GoType.PointerType github_com.goose_lang.primitive.ProphId.ty @!!
        go!"ResolveBool")) (Val #b))
    {{ (pvs' : List val), RET #(); ⌜pvs = #b :: pvs'⌝ ∗ typedPointsto l p dq ∗ proph p pvs' }} := by
  wp_start as ⟨Hl, Hp⟩
  wp_auto
  wp_apply github_com.goose_lang.primitive.ProphId.wp_ResolveBool $$ Hp as %pvs' ⟨%Hpvs, Hp⟩
  iapply HΦ
  iframe
  ipureintro; exact Hpvs

theorem GetAny.wp_proof (wp_Get : KV__Get.spec (GF := GF)) : GetAny.spec (GF := GF) := by
  intro kv γ k Q
  wp_start as ⟨#Hkv, HAU⟩
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_NewProph as %pvs %p Hp
  -- the first read: the update fires if the prophecy says its answer is returned
  wp_apply (wp_Get kv γ k (firstRead γ k pvs Q)) $$ [$Hkv HAU] as %v1 H1
  · iintro %m Hst
    by_cases hw : firstWins pvs
    · imod HAU with ⟨%m', Hst', Hclose⟩
      rcases m' with ⟨m', ⟨⟩⟩
      iunfold kvState at Hst Hst'
      simp only [Tele.app]
      icombine Hst Hst' gives %Hagree
      obtain ⟨_, Heq⟩ := Hagree
      subst Heq
      icases Hclose with ⟨-, Hcommit⟩
      iunfold kvState at Hcommit
      imod Hcommit $$ %PUnit.unit Hst' with HQ
      imodintro
      unfold kvState firstRead
      iframe Hst
      ileft
      iframe HQ
      ipureintro; exact hw
    · imodintro
      iframe Hst
      unfold firstRead
      iright
      iframe HAU
      ipureintro; exact hw
  unfold firstRead
  icases H1 with (⟨%hw, HQ1⟩ | ⟨%hw, HAU⟩)
  · -- fired at the first read: the second is a plain read
    wp_apply (wp_Get kv γ k (fun _ => iprop(True))) $$ [$Hkv] as %v2 _
    · iintro %m Hst; imodintro; iframe
    wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
    wp_apply wp_ptr_ResolveBool $$ [$prophFirst $Hp] as %pvs' ⟨%Hpvs, -, -⟩
    have hb : decide (x % W64 2 = W64 0) = true := by
      rw [firstWins, Hpvs] at hw
      simp only [List.head?_cons, Option.some.injEq] at hw
      exact go.IntoValInj.intoVal_inj hw
    wp_if_destruct
    · iapply HΦ $$ HQ1
    · simp_all
  · -- not yet: the second read fires it (its answer is the one returned)
    wp_apply (wp_Get kv γ k Q) $$ [$Hkv HAU] as %v2 HQ2
    · iintro %m Hst
      imod HAU with ⟨%m', Hst', Hclose⟩
      rcases m' with ⟨m', ⟨⟩⟩
      iunfold kvState at Hst Hst'
      simp only [Tele.app]
      icombine Hst Hst' gives %Hagree
      obtain ⟨_, Heq⟩ := Hagree
      subst Heq
      icases Hclose with ⟨-, Hcommit⟩
      iunfold kvState at Hcommit
      imod Hcommit $$ %PUnit.unit Hst' with HQ
      imodintro
      unfold kvState
      iframe
    wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
    wp_apply wp_ptr_ResolveBool $$ [$prophFirst $Hp] as %pvs' ⟨%Hpvs, -, -⟩
    have hb : decide (x % W64 2 = W64 0) = false := by
      rw [firstWins, Hpvs] at hw
      simp only [List.head?_cons, Option.some.injEq] at hw
      cases h : decide (x % W64 2 = W64 0)
      · rfl
      · rw [h] at hw; exact absurd rfl hw
    wp_if_destruct
    · simp_all
    · iapply HΦ $$ HQ2

end proof

end prophkv
end EtcdGrove
end Perennial
