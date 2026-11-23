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


end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
