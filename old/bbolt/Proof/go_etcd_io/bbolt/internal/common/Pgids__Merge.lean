module
public import Spec.go_etcd_io.bbolt.internal.common.Pgids__Merge
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Pgids.Merge.wp_proof (hMergepgids : Mergepgids.spec (GF := GF) (hG := hG)) :
    Pgids.Merge.spec (GF := GF) (hG := hG) := by
  intro s b xs ys qa qb Hsa Hsb Hlen
  wp_start as ⟨Hs, Hb⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  · have hx : xs = [] := List.eq_nil_of_length_eq_zero (by word)
    subst hx
    ispecialize HΦ $$ %b %ys
    iapply HΦ
    iframe
    isplit
    · ipureintro; exact ⟨Hsb, by simp⟩
    · ileft; ipureintro; exact ⟨rfl, rfl, rfl⟩
  have hxne : xs ≠ [] := fun h => by subst h; simp at Hsl; word
  try wp_auto
  wp_if_destruct
  · have hy : ys = [] := List.eq_nil_of_length_eq_zero (by word)
    subst hy
    ispecialize HΦ $$ %s %xs
    iapply HΦ
    iframe
    isplit
    · ipureintro; exact ⟨Hsa, by simp⟩
    · iright; ileft; ipureintro; exact ⟨hxne, rfl, rfl, rfl⟩
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) $$ [] as %dst ⟨Hdst, -⟩
  · ipureintro; word
  try wp_auto
  wp_apply hMergepgids dst s b (List.replicate (sint.nat (s.len + b.len)) (zero_val w64))
      xs ys qa qb (by simp only [List.length_replicate]; word) Hsa Hsb $$ [Hdst Hs Hb]
    as %out ⟨%Hout, Hdst, Hs, Hb⟩
  · iframe
  try wp_auto
  rw [List.drop_eq_nil_of_le (by simp only [List.length_replicate]; word), List.append_nil]
  ispecialize HΦ $$ %dst %out
  iapply HΦ
  iframe
  isplit
  · ipureintro; exact Hout.1
  · ipureintro; exact Hout.2

end proof

end bbolt
end EtcdGrove
end Perennial
