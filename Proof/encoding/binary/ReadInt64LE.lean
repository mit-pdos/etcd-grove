/-
`binary.Read(r, binary.LittleEndian, p)` into an `*int64`, proved over Perennial's translation of
`encoding/binary` (`Read`'s fast path: `intDataSize`, `io.ReadFull`, `decodeFast`).
-/
module

public import Spec.encoding.binary.ReadInt64LE
public import Perennial.Spec.encoding.binary.littleEndian__Uint64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.binary.Assumptions]

theorem binary.ReadInt64LE.wp_proof
    (wp_Uint64 : _root_.Perennial.encoding.binary.littleEndian.Uint64.spec (GF := GF) (hG := hG)) :
    binary.ReadInt64LE.spec (GF := GF) (hG := hG) := by
  intro r p x P Q
  iintro #Hr
  wp_start as ⟨HP, Hp⟩
  wp_auto
  -- intDataSize
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %b ⟨Hb, -⟩
  · ipureintro; decide
  wp_apply Hr $$ %b %(List.replicate 8 (zero_val w8)) [Hb HP]
  · iframe Hb HP; ipureintro; rfl
  iintro %n %err ⟨%ys, Hb, %Hys, HQ⟩
  wp_auto
  cases err with
  | nil =>
    have h8 : ys.length = 8 := Hys.2 rfl
    have hd : ys ++ List.drop ys.length (List.replicate 8 (zero_val w8)) = ys ++ [] := by
      simp [h8]
    rw [hd]
    wp_auto
    -- decodeFast
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_Uint64 (zero_val _) b ys [] (DFrac.own 1) h8 $$ [Hb] as Hb
    · iexact Hb
    iapply HΦ
    iexists ys, n
    iframe HQ
    ileft
    iframe Hp
    ipureintro
    exact ⟨rfl, h8⟩
  | ok e =>
    wp_auto
    iapply HΦ
    iexists ys, n
    iframe HQ
    iright
    isplitr
    · ipureintro; nofun
    iexact Hp

end proof

end EtcdGrove
end Perennial
