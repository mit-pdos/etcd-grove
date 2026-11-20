/-
The proof of `types.ID.String` (`id.go`: `strconv.FormatUint(uint64(i), 16)`), over
`strconv.FormatUint`'s spec, with `types.idStr id = fmtUint id 16` (until 2026-11-19 a
trust-boundary axiom). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.strconv.FormatUint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- `hexNatF` with enough fuel is the base-16 digits of `n`. -/
theorem types.hexNatF_eq_baseDigits (f n : Nat) (hf : n < f) :
    types.hexNatF f n = (baseDigits 16 (by omega) n).map digitChar := by
  induction f generalizing n with
  | zero => omega
  | succ f ih =>
    rw [types.hexNatF, baseDigits]
    split
    · rfl
    · rw [List.map_append, ih (n / 16) (by omega)]
      rfl

/-- **A member id's string is `strconv.FormatUint(id, 16)`'s.** -/
theorem types.idStr_eq_fmtUint (id : w64) : types.idStr id = fmtUint id (W64 16) := by
  unfold types.idStr fmtUint
  simp only [show 2 ≤ (W64 16).toNat by decide, ↓reduceDIte]
  exact types.hexNatF_eq_baseDigits _ _ (by omega)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

theorem types.ID.String.wp_proof
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    types.ID.String.spec (GF := GF) (hG := hG) := by
  intro id
  wp_start as #Hpkg
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_FormatUint
  · ipureintro; decide
  iintro %s %hs
  wp_auto
  iapply HΦ
  ipureintro
  rw [hs, types.idStr_eq_fmtUint]

end proof

end EtcdGrove
end Perennial
