/-
`Model()` (kit.go) meets the key-value store's porcupine model spec `kvS` (notes/dsv-craq.md, P2,
P4): the state's helpers over read-only maps and slices of `pend`, `step` (`goStep` of the decoded
answer), and the pure `sim_step` (`ModelSet.lean`).

In progress: `pushPend`. Still to do: `copyMap`, `set`, `findPend`, `erasePend`, `step`, `Model`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Kit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove EtcdGrove.linkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

/-- `pushPend(p, k, v)`: a new slice, `p`'s puts with `(k, v)` appended. -/
theorem wp_pushPend (p : GoSlice) (P : List pend) (k v : GoString) (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.pushPend)) (Val #p))
        (Val #k)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [pend.mk k v]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := pend) $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hq $Hp] as %n ⟨-, Hq, -⟩
  have hn : sint.nat (p.len + W64 1) = P.length + 1 := by rw [Hl.1]; word
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate,
    show P.length + 1 - P.length = 1 by omega, List.replicate_one]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z p.len ∧ sint.Z p.len < sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_singleton] at this; word
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index q (sint.Z p.len) _ (pend.mk k v) $$ [Hq] as Hq
  · iframe Hq; ipureintro; simp only [List.length_append, List.length_singleton]; word
  rw [show (sint.Z p.len).toNat = P.length by rw [Hl.1],
    List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]
  wp_auto
  iapply HΦ
  iexact Hq

/-- `copyMap(m)`: a fresh map with `m`'s contents. -/
theorem wp_copyMap (mp : Loc) (m : GMap GoString GoString) (dq : DFrac) :
    {{ (mp ↦${dq} m : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.copyMap)) (Val #mp))
    {{ (c : Loc), RET #c; c ↦$ m ∗ mp ↦${dq} m }} := by
  wp_start as Hm
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %c Hc
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoString) (fun keys (i : Int) => iprop(
      ⌜0 ≤ i⌝ ∗ ∃ (cm : GMap GoString GoString) (kx vx : GoString),
        c_ptr ↦ c ∗ k_ptr ↦ kx ∗ v_ptr ↦ vx ∗ c ↦$ cm ∗
        ⌜∀ x, cm !! x = if x ∈ keys.take i.toNat then m !! x else none⌝))) $$ Hm
  iintro %keys %hkeys
  isplitl [c k v Hc]
  · isplitr
    · ipureintro; omega
    iexists ∅, _, _
    iframe
    ipureintro
    intro x
    simp
  isplitl []
  · imodintro
    iintro %i %key %val ⟨%hk1, %hk2⟩ ⟨%hi, %cm, %kx, %vx, Hcp, Hk, Hv, Hc, %Hcm⟩
    wp_auto
    wp_apply (wp_mapInsert go.string c cm key val) $$ [$Hc] as Hc
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; omega
    iexists _, key, val
    iframe
    ipureintro
    intro x
    rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, hk1]
    by_cases hx : x = key
    · subst hx
      simp [GMap.lookup_insert, hk2]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), Hcm x]
      simp [hx]
  · iintro ⟨%h0, %cm, %kx, %vx, Hcp, Hk, Hv, Hc, %Hcm⟩ Hm
    wp_auto
    iapply HΦ
    have hcm : cm = m := by
      apply GMap.map_eq
      intro x
      rw [Hcm x, ← hkeys.2.1, List.take_of_length_le (by omega)]
      by_cases hx : x ∈ keys
      · simp [hx]
      · rw [ite_eq_right_iff.2 (fun h => absurd h hx)]
        have h1 : ¬ (m !! x).isSome = true := fun h => hx ((hkeys.1 x).2 h)
        cases h : m !! x <;> simp_all
    rw [hcm]
    iframe

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
