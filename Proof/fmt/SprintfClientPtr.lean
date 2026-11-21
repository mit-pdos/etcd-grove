/-
Proof of `Spec/fmt/SprintfClientPtr.lean`: from Perennial's `fmt.wp_Sprintf` (fmtmodel, 2026-11-20:
Perennial's model formats `%p` of a pointer as an arbitrary string without reading memory, as Go's
`fmtPointer`, and its premise admits a pointer under `%p`; until then a trust-boundary axiom here,
item 5, client construction). Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.SprintfClientPtr
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- An argument `fmt.SprintfClientArgOkAt` its directive is `fmt.argOkAt` it (Perennial's, under
the method verbs): `ArgWf`, or a `*clientv3.Client` under `%p` (a pointer kind). -/
theorem fmt.argOkAt_of_client (d : fmt.Directive) (a : GoInterface)
    (h : fmt.SprintfClientArgOkAt d a) :
    ⊢ fmt.argOkAt (GF := GF) fmt.methodVerbs d a := by
  cases a with
  | nil => unfold _root_.Perennial.fmt.argOkAt; itrivial
  | ok ii =>
    unfold _root_.Perennial.fmt.argOkAt
    rcases h with hw | ⟨hty, hp⟩
    · ileft; ipureintro; exact hw
    · iright; iright; iright; iright
      ipureintro
      refine ⟨hp, ?_⟩
      rw [hty, go.is_underlying]
      trivial

theorem fmt.argsOkAt_of_client (ds : List fmt.Directive) (xs : List GoInterface)
    (h : fmt.SprintfClientArgsAt ds xs) :
    ⊢ fmt.argsOkAt (GF := GF) fmt.methodVerbs ds xs := by
  induction xs generalizing ds with
  | nil => cases ds <;> (unfold _root_.Perennial.fmt.argsOkAt; itrivial)
  | cons a xs ih =>
    cases ds with
    | nil =>
      unfold _root_.Perennial.fmt.argsOkAt
      obtain ⟨h1, h2⟩ := h
      isplitl []
      · iapply (fmt.argOkAt_of_client _ _ h1)
      · iapply (ih [] h2)
    | cons d ds =>
      unfold _root_.Perennial.fmt.argsOkAt
      obtain ⟨h1, h2⟩ := h
      isplitl []
      · iapply (fmt.argOkAt_of_client _ _ h1)
      · iapply (ih ds h2)

theorem fmt.SprintfClientPtr.wp_proof : fmt.SprintfClientPtr.spec (GF := GF) (hG := hG) := by
  intro format args xs dq
  iintro %Φ ⟨#Hpkg, Hsl, %Hok⟩ HΦ
  obtain ⟨ds, hds, hargs⟩ := Hok
  ihave Hargs := fmt.argsOkAt_of_client (GF := GF) ds xs hargs
  ihave Hok := _root_.Perennial.fmt.argsOk_intro (GF := GF) (mv := fmt.methodVerbs) hds $$ Hargs
  wp_apply (_root_.Perennial.fmt.wp_Sprintf format args xs dq) $$ [$Hpkg $Hsl $Hok]
    as %s ⟨Hsl, %Hs⟩
  iapply HΦ
  iframe
  ipureintro; exact Hs

end proof

end EtcdGrove
end Perennial
