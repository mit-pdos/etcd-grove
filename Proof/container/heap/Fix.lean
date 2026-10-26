/-
Proof of `Spec/container/heap/Fix.lean`. Lean-first (no Rocq counterpart); see
`Proof/container/heap/Defs.lean`.
-/
module

public import Spec.container.heap.Fix
public import Spec.container.heap.down
public import Spec.container.heap.up

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : container.heap.Assumptions]

theorem heap.Fix.wp_proof
    (hdown : heap.down.spec (GF := GF) (hG := hG))
    (hup : heap.up.spec (GF := GF) (hG := hG)) :
    heap.Fix.spec (GF := GF) (hG := hG) := by
  intro A h R E xs i Hi0 Hil
  wp_start as ⟨#Hiface, HR⟩
  ihave #Hiface' := Hiface
  iunfold heap.heapIface at Hiface'
  icases Hiface' with ⟨#HLen, -, -, -⟩
  wp_auto
  wp_bind (App (Val #(methods h.ty go!"Len" h.v)) _)
  iapply HLen $$ %xs [$HR]
  inext
  iintro %n ⟨HR, %Hn⟩
  wp_auto
  wp_apply (hdown A h R E xs i n Hi0 Hil Hn) $$ [$Hiface $HR] as %b ⟨%ys, HR, %Hys⟩
  cases b
  · wp_auto
    wp_apply (hup A h R E ys i Hi0 (by rw [Hys.length_eq]; exact Hil)) $$ [$Hiface $HR]
      as ⟨%zs, HR, %Hzs⟩
    iapply HΦ
    iexists zs
    iframe
    ipureintro; exact Hzs.trans Hys
  · wp_auto
    iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hys

end proof

end EtcdGrove
end Perennial
