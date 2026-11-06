/-
`writeMeta`'s buffer in the heap (U10 of `notes/bbolt-proof-plan.md`): a zeroed page read as a
zero header and a zero meta (what `Meta.Write` takes), and the written header and meta back as
the bytes `metaBuf mv` (what `WriteAt` takes); the header again from those bytes (the error
path's `p.Id()`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.AllocPage
public import Proof.go_etcd_io.bbolt.Commit.MetaBuf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section page
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit [GooseSemantics] go_gctx sem package_sem in
theorem bytesPointsto_lt_maxAddr (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜l.addr < maxAddr⌝ ∗ bytesPointsto l dq bs := by
  cases bs with
  | nil => exact absurd rfl h
  | cons b bs =>
    simp only [bytesPointsto]
    iintro ⟨Hb, Hbs⟩
    ihave %H := heapPointsto_lt_maxAddr $$ Hb
    iframe
    ipureintro; exact H

/-- **A zeroed page as `Meta.Write`'s arguments**: a zero header, a zero meta after it (below
`maxAddr`), zeros after that. -/
theorem zeroPage_meta (l : Loc) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l (DFrac.own 1) (List.replicate 4096 (W8 0)) ⊢
      ⌜l.addr + 16 < maxAddr⌝ ∗ l ↦ zeroHdr ∗
        (l +ₗ 16) ↦ (decode (List.replicate 64 (W8 0)) : Meta) ∗
        bytesPointsto (l +ₗ 80) (DFrac.own 1) (List.replicate 4016 (W8 0)) := by
  rw [show List.replicate 4096 (W8 0) = List.replicate 16 (W8 0) ++
      (List.replicate 64 (W8 0) ++ List.replicate 4016 (W8 0)) by
    simp only [List.replicate_append_replicate]]
  iintro H
  icases (bytesPointsto_app _ _ _ _).1 $$ H with ⟨Hh, H⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ H with ⟨Hm, Hr⟩
  simp only [List.length_replicate]
  have hl16 : 0 < (l +ₗ ((16 : Nat) : Int)).addr := by simp only [Loc.add]; omega
  icases bytesPointsto_lt_maxAddr _ _ _ (by simp) $$ Hm with ⟨%Hb, Hm⟩
  icases (bytesPointsto_typed (V := Page) _ _ _ (by simp) hl).1 $$ Hh with Hh
  icases (bytesPointsto_typed (V := Meta) _ _ _ (by simp) hl16).1 $$ Hm with Hm
  have e : l +ₗ ((16 : Nat) : Int) +ₗ ((64 : Nat) : Int) = l +ₗ 80 := by
    rw [loc_add_assoc]; rfl
  rw [e]
  isplitr
  · ipureintro; simp only [Loc.add] at Hb; omega
  iframe

/-- **The written header and meta are the bytes `metaBuf mv`.** -/
theorem metaPage_bytes (l : Loc) (mv : Meta) (hl : 0 < l.addr) :
    l ↦ metaHdr mv ∗ (l +ₗ 16) ↦ metaSummed mv ∗
        bytesPointsto (l +ₗ 80) (DFrac.own 1) (List.replicate 4016 (W8 0)) ⊢
      bytesPointsto (GF := GF) l (DFrac.own 1) (metaBuf mv) := by
  iintro ⟨Hh, Hm, Hr⟩
  have hl16 : 0 < (l +ₗ (16 : Int)).addr := by simp only [Loc.add]; omega
  icases (typedPointsto_bytes (V := Page) _ _ _ hl).1 $$ Hh with Hh
  icases (typedPointsto_bytes (V := Meta) _ _ _ hl16).1 $$ Hm with Hm
  unfold metaBuf
  rw [List.append_assoc]
  iapply (bytesPointsto_app _ _ _ _).2
  rw [ByteEncoding.encode_length]
  iframe Hh
  iapply (bytesPointsto_app _ _ _ _).2
  rw [ByteEncoding.encode_length]
  have e : l +ₗ ((16 : Nat) : Int) +ₗ ((64 : Nat) : Int) = l +ₗ 80 := by
    rw [loc_add_assoc]; rfl
  rw [e]
  iframe

/-- **The header of `metaBuf mv`'s bytes** (and back). -/
theorem metaBuf_hdr (l : Loc) (mv : Meta) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l (DFrac.own 1) (metaBuf mv) ⊣⊢
      l ↦ metaHdr mv ∗
        bytesPointsto (l +ₗ 16) (DFrac.own 1) (encode (metaSummed mv) ++ List.replicate 4016 (W8 0)) := by
  have e := bytesPointsto_app (GF := GF) l (DFrac.own 1) (encode (metaHdr mv))
    (encode (metaSummed mv) ++ List.replicate 4016 (W8 0))
  rw [ByteEncoding.encode_length] at e
  have t := typedPointsto_bytes (GF := GF) l (metaHdr mv) (DFrac.own 1) hl
  unfold metaBuf
  rw [List.append_assoc]
  constructor
  · iintro H
    icases e.1 $$ H with ⟨H1, H2⟩
    iframe H2
    iapply t.2; iexact H1
  · iintro ⟨H1, H2⟩
    iapply e.2
    iframe H2
    iapply t.1; iexact H1

end page

end bbolt
end EtcdGrove
end Perennial
