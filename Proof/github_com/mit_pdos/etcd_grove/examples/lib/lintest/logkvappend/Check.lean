/-
Lean-first (no Rocq counterpart).

The proof of `Check`: `Run`'s premises, met by the fresh server (`New`), its method value
`s.Apply` (`Server.Apply.spec`, no invariant of its own: `Eapp = ∅`), its model (`Model`), the
generator closure (`genSpec`: `vals[RandomUint64() % 8]` is in bounds (`randIndex_bounds`), and it
returns a boxed `Op`, `regInOk`, whichever its kind; the slice `vals` it reads is made read-only for it) and the
caller's clock.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvappend.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvappend.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvappend.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvappend.Server__Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Run
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RandCount

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvappend

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvappend.Assumptions]

theorem Check.wp_proof
    (wp_Run : lintest.Run.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_New : New.spec (GF := GF) (hG := hG))
    (wp_Apply : Server.Apply.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro clockVal t0 Eclk clock clients ops dur HN H0 H31 Hops Hmul
  wp_start as ⟨#Hcc, #Hclk, Ht0⟩
  wp_auto
  wp_apply wp_New as %s ⟨%γ, #Hs, Hst⟩
  wp_apply wp_slice_literal (V := GoString)
    [go!"a", go!"b", go!"c", go!"d", go!"e", go!"f", go!"g", go!"h"]
  isplitr
  · ipureintro; rfl
  iintro %vp ⟨Hvals, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (8 : Int) 0) 0 = 8 from rfl]
  wp_auto
  ipersist vals
  imod ownSlice_persist $$ Hvals with #Hvals
  wp_apply wp_Model as %m #Hm
  ihave #Happ := wp_Apply γ s $$ Hpkg Hs
  wp_apply wp_Run GoString regS m _ _ clock regInOk (regState γ) clockVal t0 ∅ Eclk clients ops
    dur (by simp) HN H0 H31 Hops Hmul $$ [Hst Ht0]
  · iframe
    iframe #
    -- `gen`
    unfold genSpec
    iintro %id
    iintro !> %Φ' %Hid HΦ'
    wp_auto
    wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %rk _
    wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %rv _
    have Hr : 0 ≤ sint.Z (rv % W64 8) ∧ sint.Z (rv % W64 8) < sint.Z (W64 8) :=
      randIndex_bounds rv 8 (by decide) (by decide)
    simp only [Hr, and_self, ite_true]
    have Hi : (sint.Z (rv % W64 8)).toNat < 8 := by
      have := Hr.2; simp only [show sint.Z (W64 8) = 8 from rfl] at this; omega
    wp_apply wp_load_slice_index _ (sint.Z (rv % W64 8))
      [go!"a", go!"b", go!"c", go!"d", go!"e", go!"f", go!"g", go!"h"] _
      ([go!"a", go!"b", go!"c", go!"d", go!"e", go!"f", go!"g", go!"h"][
        (sint.Z (rv % W64 8)).toNat]'(by simpa using Hi)) Hr.1 $$ [$Hvals] as _
    · ipureintro; exact List.getElem?_eq_getElem _
    iapply HΦ'
    imodintro
    ipureintro
    exact ⟨_, _, _, rfl⟩
  iintro %r %Hr
  wp_auto
  iapply HΦ
  ipureintro
  exact Hr

end proof

end logkvappend
end lintest
end EtcdGrove
end Perennial
