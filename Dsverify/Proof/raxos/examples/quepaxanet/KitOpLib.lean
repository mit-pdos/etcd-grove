/-
`Op`'s helpers (`kit.go`'s `command`, `result`) and the logic of an answer (the lab's
`Kit/{Client,OpCore}.lean`): the update registered with remote's postcondition also records that the
output is a step's (`withStep`); the answer's result string parses back to that output
(`resultOf_ansOf`), which the codec can encode (`qOutOk`: its value is part of a fit batch).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitRecv
public import Dsverify.Proof.raxos.examples.quepaxanet.KitGen

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure raxos.msg

/-! ## The answer's parsing (`result`, without checks) -/

section pure
variable [GooseExts]

/-- `kit.go`'s `result(false, in, rep)` on the answer's one command `r`. -/
def resultOf (i : KIn) (r : GoString) : KOut :=
  if i.put then ⟨false, []⟩
  else if r.drop (1 + keyLen) = go!"nil" then ⟨false, []⟩ else ⟨true, r.drop (1 + keyLen)⟩

theorem resultOf_ansOf (i : KIn) (hi : inputOk i) (σ : raxos.pure.Store)
    (hv : ∀ v, (kvB.step i σ).2 = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil") :
    1 + keyLen ≤ (ansOf i (kvB.step i σ).2).length ∧
      resultOf i (ansOf i (kvB.step i σ).2) = (kvB.step i σ).2 := by
  obtain ⟨put, k, v⟩ := i
  obtain ⟨hk, -⟩ := hi
  simp only at hk
  cases put with
  | true =>
    simp [ansOf, resultOf, kvB, hk, keyLen]
  | false =>
    simp only [kvB, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    cases hσ : σ k with
    | none =>
      have hd : (go!"1" ++ k ++ go!"nil").drop (1 + keyLen) = go!"nil" := by
        rw [← hk, List.append_assoc, List.drop_append, List.drop_append]; simp
      refine ⟨by simp [ansOf, hk, keyLen], ?_⟩
      simp only [ansOf, resultOf, Bool.false_eq_true, ↓reduceIte, hd]
    | some w =>
      rw [hσ] at hv
      have hd : (go!"1" ++ k ++ w).drop (1 + keyLen) = w := by
        rw [← hk, List.append_assoc, List.drop_append, List.drop_append]; simp
      refine ⟨by simp [ansOf, hk, keyLen], ?_⟩
      simp only [ansOf, resultOf, Bool.false_eq_true, ↓reduceIte, hd, (hv w rfl).2]

/-- A result in a batch is no longer than the batch's encoding. -/
theorem cmd_len_le (b : Batch) (r : GoString) (h : b.cmds = [r]) :
    r.length ≤ (encBatch b).length := by
  unfold encBatch encSingle fStr fBytes
  rw [h]
  by_cases hr : r = [] <;> simp [hr] <;> omega

/-- The output a fit answer's result parses to fits the codec. -/
theorem qOutOk_of_ans (i : KIn) (hi : inputOk i) (σ : raxos.pure.Store) (b : Batch)
    (hb : b.cmds = [ansOf i (kvB.step i σ).2]) (hfit : batchFit b) :
    qOutOk (kvB.step i σ).2 := by
  have h1 := cmd_len_le b _ hb
  have h2 := hfit.2
  unfold qOutOk
  obtain ⟨put, k, v⟩ := i
  cases put with
  | true => simp [kvB]
  | false =>
    simp only [kvB, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    cases hσ : σ k with
    | none => simp
    | some w =>
      simp only [hσ] at h1 ⊢
      have hk := hi.1
      simp only [keyLen] at hk
      simp only [ansOf, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
        at h1
      omega

end pure

section helpers
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : raxos.examples.quepaxanet.Assumptions]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

theorem wp_command (i : KIn) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.command)) (Val #(In.mk i.put i.k i.v)))
    {{ RET #(cmdOf i); True }} := by
  obtain ⟨put, k, v⟩ := i
  cases put <;> wp_start <;> wp_auto <;> simp only [cmdOf, Bool.false_eq_true, ↓reduceIte] <;>
    wp_end

/-- The Go value of an output. -/
abbrev outOf (o : KOut) : Out := Out.mk false o.found o.v

theorem wp_result (i : KIn) (rep : Loc) (dq : DFrac) (b : Batch)
    (r : GoString) (hb : b.cmds = [r]) (hr : 1 + keyLen ≤ r.length) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ repCB rep dq b }}
      (App (App (App (Val (@! raxos.examples.quepaxanet.result)) (Val #false))
        (Val #(In.mk i.put i.k i.v))) (Val #rep))
    {{ RET #(outOf (resultOf i r)); True }} := by
  rcases b with ⟨bid, bsnd, bcmds⟩
  dsimp only at hb
  subst hb
  wp_start as Hrep
  unfold repCB repCBVal repList
  icases Hrep with ⟨%xv, Hx, %ps, %hxv, Hps, %hlen, Hel⟩
  simp only [List.length_singleton] at hlen
  match ps, hlen with
  | [p], _ =>
  icases Hel with ⟨⟨%m, %hm, Hm⟩, -⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
  subst hm
  unfold repCSingle
  icases Hm with ⟨%sm, Hsm, %hsm⟩
  iStructNamed Hx
  ihave %hpl := ownSlice_len _ _ _ $$ Hps
  have hl1 : xv.Messages'.len = W64 1 := by
    simp only [List.length_singleton] at hpl; word
  wp_auto
  wp_if_destruct
  rotate_left
  · exact absurd hl1 Hif
  have hb : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z xv.Messages'.len) = True := by
    rw [hl1]; simp
  simp only [hb, ite_true]
  wp_apply wp_load_slice_index xv.Messages' (sint.Z (W64 0)) [p] _ p (by simp) $$ [Hps] with Hps
  · iframe; ipureintro; rfl
  iStructNamed Hsm
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  rw [hsm.2] at *
  wp_if_destruct
  · exfalso; simp only [keyLen] at hr; word
  obtain ⟨put, k, v⟩ := i
  cases put with
  | true =>
    simp only [resultOf, outOf, ↓reduceIte]
    wp_auto
    wp_end
  | false =>
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen2
    simp only [keyLen] at hr
    have hc : (0 ≤ sint.Z (W64 1 + W64 8) ∧
        sint.Z (W64 1 + W64 8) ≤ sint.Z (W64 ↑(List.length r)) ∧
          sint.Z (W64 ↑(List.length r)) ≤ ↑(List.length r)) = True := by
      simp only [eq_iff_iff, iff_true]; refine ⟨by word, by word, by word⟩
    have hv : (List.take (sint.nat (W64 ↑(List.length r)) - sint.nat (W64 1 + W64 8))
        (List.drop (sint.nat (W64 1 + W64 8)) r)) = r.drop (1 + keyLen) := by
      have h1 : sint.nat (W64 1 + W64 8) = 1 + keyLen := by simp only [keyLen]; word
      have h2 : sint.nat (W64 ↑(List.length r)) = r.length := by word
      rw [h1, h2, List.take_of_length_le (by simp [keyLen])]
    simp only [hc, ite_true, hv]
    wp_auto
    simp only [resultOf, outOf, Bool.false_eq_true, ↓reduceIte]
    wp_if_destruct
    · rw [if_pos Hif]; wp_end
    · rw [if_neg Hif]; wp_end

end helpers

end raxos.examples.quepaxanet
end Perennial
