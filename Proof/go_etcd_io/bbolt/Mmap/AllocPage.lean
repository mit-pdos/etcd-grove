/-
The page `db.allocate` builds (U4c, `notes/bbolt-proof-plan.md`): a zeroed byte slice (the page
pool's, or a new one) whose first 16 bytes are read as a zero `Page` header (`zeroBuf_page`), and,
once its overflow and id are set, the bytes of the fresh page (`allocBuf_of_page`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.AllocBase
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

theorem decode_zero_hdr [GooseExts] :
    (decode (List.replicate 16 (0 : w8)) : Page) = ⟨W64 0, W16 0, W16 0, W32 0⟩ :=
  rfl

section page
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A zeroed byte slice of at least a header**: its pointer positive, a zero `Page` header at
it, and zeros after. -/
theorem zeroBuf_page (s : GoSlice) (n : Nat) (dq : DFrac) (hn : 16 ≤ n) :
    (s ↦*{dq} List.replicate n (W8 0) : IProp GF) ⊢
      ⌜0 < s.ptr.addr⌝ ∗ s.ptr ↦{dq} (⟨W64 0, W16 0, W16 0, W32 0⟩ : Page) ∗
        bytesPointsto (s.ptr +ₗ 16) dq (List.replicate (n - 16) (W8 0)) := by
  iintro Hs
  ihave %Hp := ownSlice_ptr_pos _ _ _ (by simp; omega) $$ Hs
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hp $$ Hs
    with ⟨Hb, -⟩
  rw [flatMap_encode_w8]
  rw [show List.replicate n (W8 0) = List.replicate 16 (W8 0) ++ List.replicate (n - 16) (W8 0) by
    rw [List.replicate_append_replicate]; congr 1; omega]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hr⟩
  icases (bytesPointsto_typed (V := Page) _ _ _ (by simp) Hp).1 $$ Hh with Hh
  rw [List.length_replicate]
  isplitr
  · ipureintro; exact Hp
  rw [show (W8 0) = (0 : w8) from rfl, decode_zero_hdr]
  iframe

/-- **The fresh page's bytes**: its header with id `id` and overflow `count - 1`, and the zeros
after it. -/
theorem allocBuf_of_page (l : Loc) (id : w64) (count : Nat) (hl : 0 < l.addr) :
    l ↦ (⟨id, W16 0, W16 0, W32 ((count - 1 : Nat) : Int)⟩ : Page) ∗
      bytesPointsto (l +ₗ 16) (DFrac.own 1) (List.replicate (count * 4096 - 16) (W8 0)) ⊢
    bytesPointsto (GF := GF) l (DFrac.own 1) (allocBuf id count) := by
  iintro ⟨Hh, Hr⟩
  icases (typedPointsto_bytes (V := Page) _ _ _ hl).1 $$ Hh with Hh
  unfold allocBuf
  iapply (bytesPointsto_app _ _ _ _).2
  rw [ByteEncoding.encode_length]
  iframe

end page

end bbolt
end EtcdGrove
end Perennial
