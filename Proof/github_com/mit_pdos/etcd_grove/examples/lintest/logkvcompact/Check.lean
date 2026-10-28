/-
Lean-first (no Rocq counterpart).

The proof of `Check`: `Run`'s premises, met by the fresh server (`New`), its method value
`s.Apply` (`Server.Apply.spec`, no invariant of its own: `Eapp = ∅`), its model (`Model`), the
generator closure (`genSpec`: for a client's index `id ≥ 0`, `vals[id%4]` is in bounds, and it
returns a boxed `Op`, `regInOk`; the slice `vals` it reads is made read-only for it) and the
caller's clock.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server__Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.Run

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvcompact

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

/-- `id % 4` (Go's signed remainder) of a non-negative `id` is an index of `vals`. -/
theorem srem4_bounds (id : w64) (h : 0 ≤ sint.Z id) :
    0 ≤ sint.Z (BitVec.srem id (W64 4)) ∧ sint.Z (BitVec.srem id (W64 4)) < sint.Z (W64 4) := by
  have h4 : sint.Z (W64 4) = 4 := rfl
  rw [h4]
  show 0 ≤ (BitVec.srem id (W64 4)).toInt ∧ (BitVec.srem id (W64 4)).toInt < 4
  rw [BitVec.toInt_srem, show (W64 4).toInt = 4 from rfl]
  have h' : 0 ≤ id.toInt := h
  rw [Int.tmod_eq_emod_of_nonneg h']
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

theorem Check.wp_proof
    (wp_Run : lintest.Run.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_New : New.spec (GF := GF) (hG := hG))
    (wp_Apply : Server.Apply.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro clockVal t0 Eclk clock clients ops dur HN H0 H31 Hops Hmul Hbound
  wp_start as ⟨#Hcc, #Hclk, Ht0⟩
  wp_auto
  wp_apply wp_New Hbound as %s ⟨%γ, #Hs, Hst⟩
  wp_apply wp_slice_literal (V := GoString) [go!"a", go!"b", go!"c", go!"d"]
  isplitr
  · ipureintro; rfl
  iintro %vp ⟨Hvals, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (4 : Int) 0) 0 = 4 from rfl]
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
    have Hr := srem4_bounds id Hid
    simp only [Hr, and_self, ite_true]
    have Hi : (sint.Z (BitVec.srem id (W64 4))).toNat < 4 := by
      have := Hr.2; simp only [show sint.Z (W64 4) = 4 from rfl] at this; omega
    wp_apply wp_load_slice_index _ (sint.Z (BitVec.srem id (W64 4)))
      [go!"a", go!"b", go!"c", go!"d"] _ ([go!"a", go!"b", go!"c", go!"d"][
        (sint.Z (BitVec.srem id (W64 4))).toNat]'(by simpa using Hi)) Hr.1 $$ [$Hvals] as _
    · ipureintro; exact List.getElem?_eq_getElem _
    iapply HΦ'
    imodintro
    ipureintro
    exact ⟨_, _, rfl⟩
  iintro %r %Hr
  wp_auto
  iapply HΦ
  ipureintro
  exact Hr

end proof

end logkvcompact
end lintest
end EtcdGrove
end Perennial
