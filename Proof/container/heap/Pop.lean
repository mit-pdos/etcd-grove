/-
Proof of `Spec/container/heap/Pop.lean` (prove-smallinits, 2026-11-20: `Pop` translated, over
`down`'s spec; until then the trust-boundary axiom). Lean-first.
-/
module

public import Spec.container.heap.Pop
public import Spec.container.heap.down
public import Proof.container.heap.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : container.heap.Assumptions]

theorem heap.Pop.wp_proof
    (hdown : heap.down.spec (GF := GF) (hG := hG)) :
    heap.Pop.spec (GF := GF) (hG := hG) := by
  intro A h R E xs Hne
  wp_start as ⟨#Hiface, #HPop, HR⟩
  ihave #Hiface' := Hiface
  iunfold heap.heapIface at Hiface'
  icases Hiface' with ⟨#HLen, -, #HSwap, -⟩
  iunfold heap.heapPopIface at HPop
  have Hpos : 0 < xs.length := List.length_pos_iff.mpr Hne
  wp_auto
  wp_bind (App (Val #(methods h.ty go!"Len" h.v)) _)
  iapply HLen $$ %xs [$HR]
  inext
  iintro %n ⟨HR, %Hn⟩
  wp_auto
  wp_bind (App (App (Val #(methods h.ty go!"Swap" h.v)) _) _)
  iapply HSwap $$ %xs %(W64 0) %(n - W64 1) [HR]
  · iframe; ipureintro; refine ⟨by word, by word, by word, by word⟩
  inext
  iintro HR
  wp_auto
  have Hl1 := heap.listSwap_perm xs (sint.nat (W64 0)) (sint.nat (n - W64 1))
  wp_apply (hdown A h R E _ (W64 0) (n - W64 1) (by word) (by word)
      (by rw [Hl1.length_eq]; word)) $$ [$Hiface $HR] as %b ⟨%ys, HR, %Hys⟩
  have Hyne : ys ≠ [] := by
    intro h0; subst h0; have := (Hys.trans Hl1).length_eq; simp at this; omega
  obtain ⟨zs, a, rfl⟩ : ∃ zs a, ys = zs ++ [a] :=
    ⟨_, _, (List.dropLast_concat_getLast Hyne).symm⟩
  wp_bind (App (Val #(methods h.ty go!"Pop" h.v)) _)
  iapply HPop $$ %zs %a [$HR]
  inext
  iintro %x ⟨HR, HE⟩
  wp_auto
  iapply HΦ
  iexists zs, a
  iframe
  ipureintro; exact Hys.trans Hl1

end proof

end EtcdGrove
end Perennial
