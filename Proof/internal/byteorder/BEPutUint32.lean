/-
Proof of `byteorder.BEPutUint32`'s spec here (the slice keeps its length) from Perennial's
(`internal.byteorder.BEPutUint32.spec`: its first 4 bytes become `v`'s, big-endian), which the
linking passes (`internal.byteorder.wp_BEPutUint32`). Until 2026-11-24 proved over the body of
this repository's own translation of `internal/byteorder`, now Perennial's (since its pin
b3f2fc485, for `crypto/sha1`). Lean-first (prove-authcrypto, 2026-11-21).
-/
module

public import Spec.internal.byteorder.BEPutUint32
public import Perennial.Spec.internal.byteorder.BEPutUint32

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.internal.byteorder.Assumptions]

theorem byteorder.BEPutUint32.wp_proof
    (wp_BEPutUint32 : _root_.Perennial.internal.byteorder.BEPutUint32.spec (GF := GF) (hG := hG)) :
    byteorder.BEPutUint32.spec (GF := GF) (hG := hG) := by
  intro b bs v hlen
  wp_start_folded as Hb
  rw [← List.take_append_drop 4 bs]
  wp_apply (wp_BEPutUint32 b (bs.take 4) (bs.drop 4) v
      (by simp only [List.length_append, List.length_take, List.length_drop]; omega))
    $$ [Hb] as Hb
  · iexact Hb
  iapply HΦ
  iexists _; iframe; ipureintro
  simp only [List.length_append, List.length_reverse, u32Le_length, List.length_take,
    List.length_drop]
  omega

end proof

end EtcdGrove
end Perennial
