/-
`binary.Write(w, binary.BigEndian, v)` of a `uint64`, proved over Perennial's translation of
`encoding/binary` (`Write`'s fast path: `intDataSize`, `encodeFast`, `w.Write(bs)`).
-/
module

public import Spec.encoding.binary.WriteUint64
public import Perennial.Spec.encoding.binary.bigEndian__PutUint64

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

theorem binary.WriteUint64.wp_proof
    (wp_PutUint64 : _root_.Perennial.encoding.binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG)) :
    binary.WriteUint64.spec (GF := GF) (hG := hG) := by
  intro wi v P Q
  iintro #Hw
  wp_start as HP
  wp_auto
  -- intDataSize
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %b ⟨Hb, -⟩
  · ipureintro; decide
  -- encodeFast
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_PutUint64 (zero_val _) b (List.replicate 8 (zero_val w8)) [] v rfl $$ [Hb] as Hb
  · rw [List.append_nil]; iexact Hb
  rw [List.append_nil] at *
  wp_apply Hw $$ %b [Hb HP] as %n %err HQ
  · iframe HP; unfold u64Be; iexact Hb
  iapply HΦ
  iexists n
  iexact HQ

end proof

end EtcdGrove
end Perennial
