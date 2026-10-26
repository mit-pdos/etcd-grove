/-
Proof of `Spec/container/heap/Push.lean`. Lean-first (no Rocq counterpart); see
`Proof/container/heap/Defs.lean`.
-/
module

public import Spec.container.heap.Push
public import Spec.container.heap.up

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : container.heap.Assumptions]

theorem heap.Push.wp_proof
    (hup : heap.up.spec (GF := GF) (hG := hG)) :
    heap.Push.spec (GF := GF) (hG := hG) := by
  intro A h R E xs x a
  wp_start as ⟨#Hiface, HR, Hx⟩
  ihave #Hiface' := Hiface
  iunfold heap.heapIface at Hiface'
  icases Hiface' with ⟨#HLen, -, -, #HPush⟩
  wp_auto
  wp_bind (App (Val #(methods h.ty go!"Push" h.v)) _)
  iapply HPush $$ %xs %x %a [$HR $Hx]
  inext
  iintro HR
  wp_auto
  wp_bind (App (Val #(methods h.ty go!"Len" h.v)) _)
  iapply HLen $$ %(xs ++ [a]) [$HR]
  inext
  iintro %n ⟨HR, %Hn⟩
  wp_auto
  simp only [List.length_append, List.length_singleton] at Hn
  wp_apply (hup A h R E (xs ++ [a]) (n - W64 1) (by word)
      (by simp only [List.length_append, List.length_singleton]; word))
    $$ [$Hiface $HR] as ⟨%ys, HR, %Hys⟩
  iapply HΦ
  iexists ys
  iframe
  ipureintro; exact Hys

end proof

end EtcdGrove
end Perennial
