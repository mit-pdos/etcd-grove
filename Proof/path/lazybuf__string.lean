/-
Proof of `Spec/path/lazybuf__string.lean`. Lean-first.
-/
module

public import Spec.path.lazybuf__string

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.path.Assumptions]

theorem path.lazybuf.string.wp_proof : path.lazybuf.string.spec (GF := GF) (hG := hG) := by
  intro b p P w HPl
  wp_start as Hb
  iunfold path.lbOwn at Hb
  icases Hb with ⟨%buf, Hs, Hbuf, Hwf, %Hwb, Hcase⟩
  try wp_auto
  have hw1 : sint.nat (W64 (w : Int)) = w := by word
  icases Hcase with (⟨%Hnil, %HP⟩ | ⟨⟨%Hnn, -⟩, Hsl⟩)
  · subst Hnil HP
    try wp_auto
    rw [if_pos (by refine ⟨by word, by word, by word⟩)]
    try wp_auto
    simp only [hw1, show sint.nat (W64 0) = 0 by rfl, Nat.sub_zero, List.drop_zero]
    iapply HΦ; itrivial
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hsl
    simp only [Hnn, decide_false]
    try wp_auto
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (w : Int)) ∧
        sint.Z (W64 (w : Int)) ≤ sint.Z buf.len := ⟨by word, by word, by word⟩
    rw [if_pos ⟨hb.1, hb.2.1, by omega⟩]
    icases (ownSlice_slice (W64 0) (W64 (w : Int)) buf _ P hb).1 $$ Hsl with ⟨-, Hsub, -⟩
    wp_apply wp_bytes_to_string _ _ _ $$ Hsub as -
    try wp_auto
    rw [show subslice 0 (sint.nat (W64 (w : Int))) P = P.take w by
      rw [hw1]; simp [subslice]]
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
