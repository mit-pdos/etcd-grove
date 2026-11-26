/- Lean-first (no Rocq counterpart).

# `freshValue`'s proof

`"v" + FormatUint(take(), 10) + randomWord()`: `mkVal` of the fresh id and the word.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.freshValue
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.counter__take
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.randomWord
public import Perennial.Spec.strconv.FormatUint
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem freshValue.wp_proof (wp_take : counter.take.spec (GF := GF) (hG := hG))
    (wp_randomWord : randomWord.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    freshValue.spec (GF := GF) (hG := hG) := by
  intro γid γb c
  wp_start as ⟨#Hc, Hcred⟩
  ihave #Hs : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_take γid γb c $$ [$Hc $Hcred] as %id Htok
  try wp_auto
  wp_apply wp_FormatUint id (W64 10) (by decide) (by decide) $$ [$Hs]
  try wp_auto
  wp_apply wp_randomWord as %w %Hw
  try wp_auto
  iapply HΦ
  iexists id, w
  iframe Htok
  ipureintro
  exact ⟨by simp [mkVal], Hw⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
