/-
Proof of `Spec/path/Split.lean`. Lean-first.
-/
module

public import Spec.path.Split
public import Spec.internal.bytealg.LastIndexByteString

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

theorem path.Split.wp_proof (hLast : bytealg.LastIndexByteString.spec (GF := GF) (hG := hG)) :
    path.Split.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  ihave #Hb : isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg $$ []
  · iPkgInit
  try wp_auto
  wp_apply hLast p (W8 47) as %Hl
  try wp_auto
  have hb := path.lastIndexByte_bounds p (W8 47)
  have h1 : sint.Z (W64 (path.lastIndexByte p (W8 47)) + W64 1) = path.lastIndexByte p (W8 47) + 1 := by
    word
  have h2 : sint.nat (W64 (path.lastIndexByte p (W8 47)) + W64 1) =
      (path.lastIndexByte p (W8 47) + 1).toNat := by
    word
  have h3 : sint.Z (W64 (p.length : Int)) = p.length := by word
  have h4 : sint.nat (W64 (p.length : Int)) = p.length := by word
  rw [if_pos (by rw [h1]; refine ⟨by word, by word, by omega⟩)]
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  rw [if_pos (by rw [h1, h3]; refine ⟨by omega, by omega, by word⟩)]
  try wp_auto
  simp only [path.splitModel, h2, h4, Nat.sub_zero, List.drop_zero]
  rw [List.take_of_length_le (l := List.drop _ p) (by simp)]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
