/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/vsrkv/Store.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The proofs of `examples/vsrkv`: `New`, `(*Store).Handle`, and the method value as a handler
(Go's `strings.Split`: Perennial's `strings.wp_Split`, `Perennial.Proof.strings.Link`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.vsrkv
public import Perennial.Proof.strings.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : vsrkv.Assumptions]

theorem vsrkv.wp_load_lit (sl : GoSlice) (l : List GoString) (i : Int) :
    {{ (sl ↦* l ∗ ⌜i.toNat < l.length ∧ 0 ≤ i ∧ i < 2 ^ 63⌝ : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.string))) (Val #(sliceIndexRef GoString (sint.Z (W64 i)) sl)))
    {{ RET #(l.getD i.toNat []); sl ↦* l }} := by
  iintro %Φ ⟨Hsl, %h⟩ HΦ
  have hi : sint.Z (W64 i) = i := by word
  rw [hi]
  wp_apply (wp_load_slice_index _ _ _ _ (l.getD i.toNat []) h.2.1) $$ [$Hsl] as Hsl
  · ipureintro; simp [List.getD_eq_getElem?_getD, h.1]
  iapply HΦ $$ Hsl

theorem vsrkv.New.wp_proof : vsrkv.New.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %mp Hm
  iapply HΦ
  unfold vsrkv.isStore
  iexists mp, ∅
  iframe
  ipureintro
  intro k
  simp

theorem vsrkv.Store.Handle.wp_proof : vsrkv.Store.Handle.spec (GF := GF) (hG := hG) := fun st m op => by
  wp_start as Hst
  unfold vsrkv.isStore
  icases Hst with ⟨%mp, %mm, Hst, Hm, %Hmm⟩
  wp_auto
  wp_apply _root_.Perennial.strings.wp_Split _ _ (by decide) as %sl ⟨Hsl, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [VsrModel.handle]
  generalize strings.split op [32#8] = f at Hlen ⊢
  rcases f with _ | ⟨c, _ | ⟨k, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩⟩
  all_goals simp only [List.length_cons, List.length_nil] at Hlen
  all_goals (iterate 4 (
    (repeat (first
      | (wp_apply vsrkv.wp_load_lit $$ [$Hsl] as Hsl; ipureintro; refine ⟨?_, by decide, by decide⟩; simp)
      | (rw [if_pos (c := 0 ≤ sint.Z _ ∧ sint.Z _ < sint.Z _) ⟨by decide, by word⟩])
      | (wp_apply (wp_mapInsert go.string mp mm) $$ [$Hm] as Hm)
      | (wp_apply (wp_map_lookup1 go.string go.string mp mm _ (DFrac.own 1)) $$ [$Hm] as Hm)
      | wp_auto
      | (wp_if_destruct <;> try (no_sorry (exfalso; word)))))
    all_goals (try (wp_apply vsrkv.wp_load_lit $$ [$Hsl] as Hsl; ipureintro; refine ⟨?_, by decide, by decide⟩; simp))))
  all_goals (try (rw [decide_eq_false (show ¬ (sl.len = W64 2) by word)]; wp_auto))
  all_goals (
    (try simp only [List.getD_cons_zero, List.getD_cons_succ, Int.reduceToNat] at *)
    (try simp only [List.getD, List.getElem?_cons_zero, Option.getD_some] at Hif)
    (try subst Hif)
    (try simp only [if_true, Hif, if_false])
    (try rw [Hmm k, show Perennial.zero_val GoString = [] from rfl])
    iapply HΦ
    iexists _, _
    iframe
    ipureintro)
  all_goals (try exact Hmm)
  all_goals (
    intro k1
    by_cases hk : k1 = k
    · subst hk; simp only [GMap.lookup_insert, if_true]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk, Hmm])

theorem vsrkv.Store.Handle_value.wp_proof : vsrkv.Store.Handle_value.spec (GF := GF) (hG := hG) := fun st => by
  iintro #Hpkg
  unfold vsrkv.srvOk
  iintro !> %op %m %Φ !> Hpre HΦ
  iapply (vsrkv.Store.Handle.wp_proof st m op) $$ [Hpre] HΦ
  iframe
  iexact Hpkg

end proofs
end Perennial.github_com.tangledbytes.go_vsr.examples
