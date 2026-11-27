/-
The proof of `Spec/google_golang_org/grpc/headerListTooLarge.lean`: the loop keeps the sum of the
fields so far, within the limit; each addition is of one length (below `2 ^ 63`, `len`'s
semantics) to a sum within the limit, so it does not overflow.
-/
module

public import Spec.google_golang_org.grpc.headerListTooLarge
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem natSum_take_succ : ∀ (l : List Nat) (n : Nat) (h : n < l.length),
    (l.take (n + 1)).sum = (l.take n).sum + l[n]
  | [], _, h => by simp at h
  | a :: l, 0, _ => by simp
  | a :: l, n + 1, h => by
    simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
    rw [natSum_take_succ l n (by simpa using h)]; omega

theorem natSum_take_le : ∀ (l : List Nat) (n : Nat), (l.take n).sum ≤ l.sum
  | [], _ => by simp
  | a :: l, 0 => by simp
  | a :: l, n + 1 => by
    simp only [List.take_succ_cons, List.sum_cons]
    have := natSum_take_le l n; omega

/-- The size of the first `n` fields. -/
def hlPrefix (fs : List (GoString × GoString)) (n : Nat) : Nat :=
  ((fs.take n).map fun f => 32 + f.1.length + f.2.length).sum

theorem hlPrefix_succ (fs : List (GoString × GoString)) (n : Nat) (h : n < fs.length) :
    hlPrefix fs (n + 1) = hlPrefix fs n + (32 + fs[n].1.length + fs[n].2.length) := by
  unfold hlPrefix
  rw [List.map_take, List.map_take, natSum_take_succ _ _ (by simpa using h)]
  simp

theorem hlPrefix_le (fs : List (GoString × GoString)) (n : Nat) :
    hlPrefix fs n ≤ (fs.map fun f => 32 + f.1.length + f.2.length).sum := by
  unfold hlPrefix
  rw [List.map_take]
  exact natSum_take_le _ _

theorem hlPrefix_full (fs : List (GoString × GoString)) :
    hlPrefix fs fs.length = (fs.map fun f => 32 + f.1.length + f.2.length).sum := by
  simp [hlPrefix]

theorem grpc.headerListTooLarge.wp_proof :
    grpc.headerListTooLarge.spec (GF := GF) (hG := hG) := by
  intro s hs dq
  wp_start as Hs
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave IH : iprop(∃ (n z : w64) (fv : google_golang_org.grpc.headerField),
      "i" ∷ i_ptr ↦ n ∗ "sz" ∷ sz_ptr ↦ z ∗ "f" ∷ f_ptr ↦ fv ∗ "res" ∷ «$res0_ptr» ↦ false ∗
      "Hs" ∷ s ↦*{dq} hs ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ hs.length ∧
        uint.nat z = hlPrefix (hfPairs hs) (sint.nat n) ∧
        hlPrefix (hfPairs hs) (sint.nat n) ≤ maxHeaderBlock⌝) $$ [i sz f «$res0» Hs]
  · iexists W64 0, W64 0, _
    simp only [named]
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 by decide]
    simp [hlPrefix, maxHeaderBlock]
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < hs.length := by word
    obtain ⟨h, Hh⟩ : ∃ h, hs[sint.nat n]? = some h := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index s (sint.Z n) _ dq h Hn.1 $$ [$Hs] as Hs
    · ipureintro; rw [show (sint.Z n).toNat = sint.nat n by rfl]; exact Hh
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %HlN
    obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp Hh
    have hlenP : (hfPairs hs).length = hs.length := by simp [hfPairs]
    have hpair : (hfPairs hs)[sint.nat n]'(by omega) = (h.Name', h.Value') := by
      simp [hfPairs, hget]
    have hsucc := hlPrefix_succ (hfPairs hs) (sint.nat n) (by omega)
    rw [hpair] at hsucc
    simp only at hsucc
    have htot := hlPrefix_le (hfPairs hs) (sint.nat n + 1)
    obtain ⟨-, -, hz, hPle⟩ := Hn
    unfold maxHeaderBlock at hPle
    have h16 : uint.Z (W64 16777216) = 16777216 := by rfl
    have hz1 : uint.Z (z + (W64 32 + W64 (h.Name'.length : Int))) =
        hlPrefix (hfPairs hs) (sint.nat n) + 32 + h.Name'.length := by word
    wp_if_destruct
    · -- the name goes over the limit
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      simp only [headerListOk, maxHeaderBlock]
      constructor
      · intro h; cases h
      · intro hok; rw [h16, hz1] at Hif; omega
    · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %HlV
      have hz2 : uint.Z (z + (W64 32 + W64 (h.Name'.length : Int)) + W64 (h.Value'.length : Int)) =
          hlPrefix (hfPairs hs) (sint.nat n) + 32 + h.Name'.length + h.Value'.length := by word
      wp_if_destruct
      · -- the value goes over the limit
        wp_for_post
        iapply HΦ
        iframe
        ipureintro
        simp only [headerListOk, maxHeaderBlock]
        constructor
        · intro h; cases h
        · intro hok; rw [h16, hz2] at Hif; omega
      · wp_for_post
        iframe
        iexists n + W64 1, _, h
        simp only [named]
        iframe
        ipureintro
        have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        rw [hn1]
        refine ⟨by word, by omega, ?_, ?_⟩
        · rw [hsucc]; word
        · rw [hsucc]; unfold maxHeaderBlock; word
  · -- the loop is done: the whole list is within the limit
    iapply HΦ
    iframe
    ipureintro
    have hn : sint.nat n = hs.length := by word
    obtain ⟨-, -, -, hPle⟩ := Hn
    rw [hn, show hs.length = (hfPairs hs).length by simp [hfPairs], hlPrefix_full] at hPle
    simpa [headerListOk] using hPle

end proof

end EtcdGrove
end Perennial
