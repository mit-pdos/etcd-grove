/-
`dereference`'s copies (U9b, `notes/bbolt-proof-plan.md`): `copy(dst, s)` of a slice the writer
keeps (`srcOwn`: a view slice, read through the view's cells, or persistent heap bytes), and the
length of such a slice.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section copy
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- `srcOwn_persistent`: `Inv/WtxHeap` (batch 18).

/-- A kept slice's length. -/
theorem srcOwn_len (v : View) (s : GoSlice) (src : Src) (bs : List w8) (hs : src ≠ .stale) :
    srcOwn (GF := GF) v s src bs ⊢ ⌜bs.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len⌝ := by
  cases src with
  | view =>
    unfold srcOwn
    iintro %H
    ipureintro
    obtain ⟨-, hl, hlen, -⟩ := H
    rw [hlen]
    have : sint.Z (W64 (bs.length : Int)) = bs.length := sint_Z_W64_nat _ (by omega)
    simp only [sint.nat, this]; omega
  | own dq =>
    unfold srcOwn
    iintro H
    iapply ownSlice_len $$ H
  | stale => exact absurd rfl hs

/-- A kept slice, read: its bytes at some fraction (from the view's cells, or persistent). -/
theorem srcOwn_read (q : Qp) (v : View) (s : GoSlice) (src : Src) (bs : List w8)
    (hs : src ≠ .stale) (hne : bs ≠ []) :
    viewCells (GF := GF) q v ∗ srcOwn v s src bs ⊢
      ∃ dq, s ↦*{dq} bs ∗ (s ↦*{dq} bs -∗ viewCells q v) := by
  cases src with
  | view =>
    unfold srcOwn
    iintro ⟨Hv, %H⟩
    obtain ⟨hloc, hl, hlen, hcap⟩ := H
    icases viewCells_loc_acc q v s.ptr bs hloc $$ Hv with ⟨%dq, Hb, Hback⟩
    ihave %Hbnd := internal.common.bytesPointsto_in_bounds _ _ _ hne $$ Hb
    have hs' : s = slice.mk s.ptr (W64 (bs.length : Int)) (W64 (bs.length : Int)) := by
      cases s; simp_all
    iexists dq
    icases (internal.common.bytesPointsto_ownSlice s.ptr dq bs Hbnd.1 (by omega)).1 $$ Hb with Hb
    rw [← hs']
    iframe Hb
    iintro Hb
    iapply Hback
    iapply (internal.common.bytesPointsto_ownSlice s.ptr dq bs Hbnd.1 (by omega)).2
    rw [← hs']
    iexact Hb
  | own dq =>
    unfold srcOwn
    iintro ⟨Hv, #Hs⟩
    iexists DFrac.discard
    iframe Hs
    iintro -
    iexact Hv
  | stale => exact absurd rfl hs

/-- **`copy(dst, s)` of a kept slice** into a zeroed slice of its length: `dst` holds its bytes. -/
theorem wp_copy_kept (q : Qp) (v : View) (dst s : GoSlice) (src : Src) (bs : List w8)
    (hs : src ≠ .stale) :
    {{ dst ↦* List.replicate bs.length (W8 0) ∗ viewCells (GF := GF) q v ∗ srcOwn v s src bs }}
      (App (App (Val #(functions go.copy [go.GoType.SliceType go.byte])) (Val #dst)) (Val #s))
    {{ (k : w64), RET #k; dst ↦* bs ∗ viewCells q v }} := by
  iintro %Φ ⟨Hd, Hv, #Hs⟩ HΦ
  ihave %Hl := srcOwn_len v s src bs hs $$ Hs
  by_cases hne : bs = []
  · subst hne
    have h0 : s.len = W64 0 := by
      obtain ⟨h1, h2⟩ := Hl
      simp only [List.length_nil] at h1
      word
    wp_apply wp_slice_copy_of_len_zero (V := w8) dst s h0
    iapply HΦ
    iframe
  · icases srcOwn_read q v s src bs hs hne $$ [$Hv $Hs] with ⟨%dq, Hb, Hback⟩
    wp_apply wp_slice_copy (V := w8) dst _ s bs dq $$ [$Hd $Hb] as %k ⟨-, Hd, Hb⟩
    iapply HΦ
    rw [List.length_replicate, List.take_length, List.drop_replicate, Nat.sub_self,
      List.replicate_zero, List.append_nil]
    iframe
    iapply Hback $$ Hb

end copy

end bbolt
end EtcdGrove
end Perennial
