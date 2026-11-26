/-
The proof of `Spec/encoding/binary/bigEndian__AppendUint32.lean`: load the global `BigEndian` (as
Perennial's `wp_BigEndian_PutUint32_of`), then the value method's translated body: a slice literal
of `v`'s four bytes, appended.
-/
module

public import Spec.encoding.binary.bigEndian__AppendUint32

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

open encoding.binary in
theorem binary.bigEndian.AppendUint32.wp_proof :
    binary.bigEndian.AppendUint32.spec (GF := GF) (hG := hG) := by
  intro b vs v
  wp_start as ⟨Hb, Hcap⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hinit := isInit_access $$ Hpkg
  icases Hinit with ⟨-, #Hbe, -⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hbe
  wp_apply (wp_load_struct_nofields (V := bigEndian) _ Hnn) as -
  wp_method_call
  wp_call
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) (u32Le v).reverse
  wp_auto
  isplitl []
  · ipureintro
    rw [u32Le_4]; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_apply wp_slice_append (V := w8) b vs _ (u32Le v).reverse (DFrac.own 1) $$ [$Hb $Hcap $Hsl]
    as %r ⟨Hr, Hrcap, -⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
