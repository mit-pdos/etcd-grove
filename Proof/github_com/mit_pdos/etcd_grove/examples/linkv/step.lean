/-
Lean-first (no Rocq counterpart).

The proof of `step`: its cases are `stepL`'s; a new slice (`set`'s, `insertSorted`'s) is made
read-only for `cfgOwn`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.step
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.set
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.insertSorted

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

set_option hygiene false in
/-- `step` returns `nil` (`stepL g x y = []`, proved by `h`). -/
local macro "step_nil" h:term : tactic => `(tactic| (
  rw [show stepL g x y = [] from $h]
  ihave Hn := ownSlice_nil (V := kvConfig) (GF := GF) (DFrac.own 1)
  iapply HΦ
  isplitl [Hn]
  · iexact Hn
  · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
    iempintro))

set_option hygiene false in
/-- `step` returns `[]kvConfig{c}` (`stepL g x y = [g]`, proved by `h`). -/
local macro "step_one" h:term : tactic => `(tactic| (
  wp_apply wp_slice_literal (l := [c])
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hl1, _⟩
  wp_auto
  iapply HΦ
  rw [show stepL g x y = [g] from $h]
  iframe
  iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
  isplit
  · iexact Hck
  · iexact Hcp))

theorem step.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_set : set.spec (GF := GF) (hG := hG))
    (wp_insertSorted : insertSorted.spec (GF := GF) (hG := hG)) :
    step.spec (GF := GF) (hG := hG) := by
  intro c g x y
  wp_start as ⟨#Hc, %Hb⟩
  unfold cfgOwn
  icases Hc with ⟨#Hck, #Hcp⟩
  wp_auto
  cases hP : x.Put'
  · wp_auto
    cases hE : y.Err'
    · wp_auto
      wp_apply wp_lookup c.kv' g.kv DFrac.discard x.Key' $$ [$Hck] as %v %ok ⟨-, %Hlk⟩
      have hr : lookupL g.kv x.Key' = (v, ok) := Hlk.symm
      cases ok <;> cases hF : y.Found'
      · -- not found, `Found` false: the value must be empty
        wp_auto
        wp_if_destruct
        · step_one (by simp [stepL, hP, hE, hr, hF, Hif])
        · step_nil (by simp [stepL, hP, hE, hr, hF, Hif])
      · wp_auto
        step_nil (by simp [stepL, hP, hE, hr, hF])
      · wp_auto
        step_nil (by simp [stepL, hP, hE, hr, hF])
      · -- found, `Found` true: the values must agree
        wp_auto
        wp_if_destruct
        · step_one (by simp [stepL, hP, hE, hr, hF])
        · step_nil (by simp [stepL, hP, hE, hr, hF, Hif])
    · wp_auto
      step_one (by simp [stepL, hP, hE])
  · wp_auto
    cases hE : y.Err'
    · wp_auto
      cases hF : y.Found'
      · wp_auto
        wp_if_destruct
        · wp_apply wp_set c.kv' g.kv DFrac.discard x.Key' x.Val' $$ [$Hck] as %nk ⟨-, Hnk, -⟩
          · ipureintro; exact Hb.1
          ipersist Hnk
          wp_apply wp_slice_literal (l := [(⟨nk, c.pend'⟩ : kvConfig)])
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hl1, _⟩
          wp_auto
          iapply HΦ
          rw [show stepL g x y = [⟨setL g.kv x.Key' x.Val', g.pend⟩] by
            simp [stepL, hP, hE, hF, Hif]]
          iframe
          iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
          isplit
          · iexact Hnk
          · iexact Hcp
        · step_nil (by simp [stepL, hP, hE, hF, Hif])
      · wp_auto
        step_nil (by simp [stepL, hP, hE, hF])
    · wp_auto
      wp_apply wp_insertSorted c.pend' g.pend DFrac.discard ⟨x.Key', x.Val'⟩ $$ [$Hcp] as %np ⟨-, Hnp, -⟩
      · ipureintro; exact Hb.2
      ipersist Hnp
      wp_apply wp_slice_literal (l := [(⟨c.kv', np⟩ : kvConfig)])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_auto
      iapply HΦ
      rw [show stepL g x y = [⟨g.kv, insertSortedL g.pend ⟨x.Key', x.Val'⟩⟩] by
        simp [stepL, hP, hE]]
      iframe
      iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
      isplit
      · iexact Hck
      · iexact Hnp

end proof

end linkv
end EtcdGrove
end Perennial
