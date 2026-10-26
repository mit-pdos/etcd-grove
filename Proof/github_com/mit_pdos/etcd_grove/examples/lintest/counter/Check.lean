/-
Lean-first (no Rocq counterpart).

The proof of `Check`: `Run`'s premises, met by the fresh counter (`New`), its method value
`c.Apply` (`Counter.Apply.spec`, no invariant of its own: `Eapp = ∅`), its model (`Model`), the
generator closure (`genSpec`: it returns a boxed `bool`, `counterInOk`) and the caller's clock.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Counter__Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.Run

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

theorem Check.wp_proof
    (wp_Run : lintest.Run.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_New : New.spec (GF := GF) (hG := hG))
    (wp_Apply : Counter.Apply.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro clockVal t0 Eclk clock clients ops dur HN H0 H31 Hops Hmul
  wp_start as ⟨#Hcc, #Hclk, Ht0⟩
  wp_auto
  wp_apply wp_New as %c ⟨%γ, #Hc, Hs⟩
  wp_apply wp_Model as %m #Hm
  ihave #Happ := wp_Apply γ c $$ Hpkg Hc
  wp_apply wp_Run w64 counterS m _ _ clock counterInOk (counterState γ) clockVal t0 ∅ Eclk clients ops dur
    (by simp) HN H0 H31 Hops Hmul $$ [Hs Ht0]
  · iframe
    iframe #
    -- `gen`
    unfold genSpec
    iintro %id
    iintro !> %Φ' _ HΦ'
    wp_auto
    iapply HΦ'
    imodintro
    ipureintro
    exact ⟨_, rfl⟩
  iintro %r %Hr
  wp_auto
  iapply HΦ
  ipureintro
  exact Hr

end proof

end counter
end lintest
end EtcdGrove
end Perennial
